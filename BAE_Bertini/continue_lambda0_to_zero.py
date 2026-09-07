import argparse
import ast
import csv
import re
import sys
import time
from fractions import Fraction
from pathlib import Path

import bertini
from bertini.function_tree import symbol


DEFAULT_INPUT = Path("data/{2, 0}_{{1, 3, 4, 5}, {2, 6}}.csv")
REQUIRED_COLUMNS = ("var", "Initialvar", "expression")
MATHEMATICA_SCIENTIFIC_RE = re.compile(
    r"(?<![A-Za-z0-9_.])([+-]?(?:\d+(?:\.\d*)?|\.\d+))(?:`\d+(?:\.\d*)?)?\*(?:10)?\^([+-]?\d+)"
)


def rational(value):
    return symbol.Rational(str(value))


def stepping_rational(value):
    fraction = Fraction(str(value))
    return bertini.multiprec.Rational(fraction.numerator, fraction.denominator)


def sanitize_for_filename(value):
    text = str(value).strip()
    text = re.sub(r"[^A-Za-z0-9_.-]+", "_", text)
    return text.strip("_") or "value"


def normalize_mathematica_number_text(text):
    text = str(text)
    text = MATHEMATICA_SCIENTIFIC_RE.sub(r"\1e\2", text)
    text = re.sub(r"(?<=\d)`\d+(?:\.\d*)?", "", text)
    return text


def bertini_complex_text(value):
    return repr(value)


def bertini_complex_real_text(value):
    text = bertini_complex_text(value).strip()
    match = re.match(r"^\(([^,]+),", text)
    if match:
        return match.group(1).strip()
    return str(value)


def parse_expression(expression, namespace):
    """Parse one CSV expression into a Bertini symbolic expression."""
    expression = normalize_mathematica_number_text(expression)

    def number_text(node):
        return ast.get_source_segment(expression, node) or str(node.value)

    def build(node):
        if isinstance(node, ast.Expression):
            return build(node.body)
        if isinstance(node, ast.Name):
            if node.id not in namespace:
                raise ValueError(f"Unknown symbol {node.id!r} in expression {expression!r}")
            return namespace[node.id]
        if isinstance(node, ast.Constant):
            if not isinstance(node.value, (int, float)):
                raise ValueError(f"Unsupported constant {node.value!r}")
            return rational(number_text(node))
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -build(node.operand)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.UAdd):
            return build(node.operand)
        if isinstance(node, ast.BinOp):
            left = build(node.left)
            right = build(node.right)
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
            if isinstance(node.op, ast.Div):
                return left / right
            if isinstance(node.op, ast.Pow):
                if not isinstance(node.right, ast.Constant) or not isinstance(node.right.value, int):
                    raise ValueError("Only integer powers are supported")
                return left ** node.right.value
        raise ValueError(f"Unsupported expression piece: {ast.dump(node)}")

    return build(ast.parse(expression, mode="eval"))


def parameter_path(start_value, target_value, path_variable):
    """Return p(t) with p(1)=start_value and p(0)=target_value."""
    start = rational(start_value)
    target = rational(target_value)
    return target + (start - target) * path_variable


def validate_rows(input_path, rows, lambda_column):
    if not rows:
        raise ValueError(f"No rows found in {input_path}")

    missing = [column for column in REQUIRED_COLUMNS if column not in rows[0]]
    if missing:
        raise ValueError(f"{input_path} is missing required columns: {', '.join(missing)}")

    if lambda_column not in rows[0]:
        raise ValueError(f"{input_path} is missing lambda column {lambda_column!r}")

    lambda_values = {row[lambda_column] for row in rows}
    if len(lambda_values) != 1:
        raise ValueError(
            f"Expected one {lambda_column} value in {input_path}, found {sorted(lambda_values)}"
        )


def load_problem(input_path, lambda_column, parameter_symbol, target_value, path_symbol):
    with input_path.open(newline="") as csv_file:
        rows = list(csv.DictReader(csv_file))

    validate_rows(input_path, rows, lambda_column)

    variable_names = [row["var"] for row in rows]
    lambda_start = rows[0][lambda_column]

    if path_symbol in variable_names:
        raise ValueError(
            f"Path variable {path_symbol!r} collides with a CSV variable. "
            "Pass a different name with --path-symbol."
        )

    variables = {name: bertini.Variable(name) for name in variable_names}
    path_variable = bertini.Variable(path_symbol)
    moving_parameter = parameter_path(lambda_start, target_value, path_variable)

    namespace = dict(variables)
    namespace[parameter_symbol] = moving_parameter
    if lambda_column.isidentifier():
        namespace[lambda_column] = moving_parameter

    system = bertini.System()
    group = bertini.VariableGroup()
    for name in variable_names:
        group.append(variables[name])
    system.add_variable_group(group)

    for row in rows:
        system.add_function(parse_expression(row["expression"], namespace))
    system.add_path_variable(path_variable)

    start_point = bertini.multiprec.Vector(system.num_variables())
    for index, row in enumerate(rows):
        start_point[index] = bertini.multiprec.Complex(
            normalize_mathematica_number_text(row["Initialvar"])
        )

    return rows, variable_names, lambda_start, system, start_point


def continue_parameter(
    system,
    start_point,
    tracking_tolerance,
    infinite_tolerance,
    max_precision=None,
    max_num_steps=None,
    initial_step_size=None,
    max_step_size=None,
    max_newton_iterations=None,
    predictor=None,
):
    tracker = bertini.tracking.AMPTracker(system)
    tracker.tracking_tolerance(tracking_tolerance)
    tracker.infinite_truncation_tolerance(infinite_tolerance)

    if max_precision is not None:
        amp_config = bertini.tracking.config.amp_config_from(system)
        amp_config.maximum_precision = max_precision
        tracker.precision_setup(amp_config)

    if any(value is not None for value in (max_num_steps, initial_step_size, max_step_size)):
        stepping = tracker.get_stepping()
        if max_num_steps is not None:
            stepping.max_num_steps = max_num_steps
        if initial_step_size is not None:
            stepping.initial_step_size = stepping_rational(initial_step_size)
        if max_step_size is not None:
            stepping.max_step_size = stepping_rational(max_step_size)
        tracker.set_stepping(stepping)

    if max_newton_iterations is not None:
        newton = tracker.get_newton()
        newton.max_num_newton_iterations = max_newton_iterations
        tracker.set_newton(newton)

    if predictor is not None:
        try:
            predictor_value = getattr(bertini.tracking.Predictor, predictor)
        except AttributeError as exc:
            choices = ", ".join(sorted(bertini.tracking.Predictor.names))
            raise ValueError(f"Unknown predictor {predictor!r}. Choices: {choices}") from exc
        tracker.predictor(predictor_value)

    endpoint = bertini.multiprec.Vector(system.num_variables())
    status = tracker.track_path(
        result=endpoint,
        start_time=bertini.multiprec.Complex("1"),
        end_time=bertini.multiprec.Complex("0"),
        start_point=start_point,
    )
    residual = system.eval(endpoint, bertini.multiprec.Complex("0"))
    return status, endpoint, residual


def default_output_path(input_path, output_dir, lambda_column, target_value):
    suffix = f"{sanitize_for_filename(lambda_column)}_to_{sanitize_for_filename(target_value)}"
    return output_dir / f"{input_path.stem}_{suffix}_solution.csv"


def write_result(
    output_path,
    input_path,
    rows,
    variable_names,
    lambda_column,
    parameter_symbol,
    lambda_start,
    target_value,
    start_point,
    endpoint,
    residual,
    status,
):
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", newline="") as csv_file:
        fieldnames = [
            "source_file",
            "syt",
            "var",
            "lambda_column",
            "parameter_symbol",
            "parameter_start",
            "parameter_end",
            "initial_value",
            "final_value",
            "residual_at_parameter_end",
            "status",
        ]
        writer = csv.DictWriter(csv_file, fieldnames=fieldnames)
        writer.writeheader()
        for index, name in enumerate(variable_names):
            writer.writerow(
                {
                    "source_file": str(input_path),
                    "syt": rows[index].get("syt", ""),
                    "var": name,
                    "lambda_column": lambda_column,
                    "parameter_symbol": parameter_symbol,
                    "parameter_start": lambda_start,
                    "parameter_end": target_value,
                    "initial_value": bertini_complex_text(start_point[index]),
                    "final_value": bertini_complex_text(endpoint[index]),
                    "residual_at_parameter_end": bertini_complex_text(residual[index]),
                    "status": status,
                }
            )


def write_legacy_result(output_path, variable_names, endpoint):
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", newline="") as csv_file:
        writer = csv.DictWriter(csv_file, fieldnames=["var", "b_final_value"])
        writer.writeheader()
        for name, value in zip(variable_names, endpoint):
            writer.writerow(
                {
                    "var": name,
                    "b_final_value": bertini_complex_real_text(value),
                }
            )


def write_timing_file(output_path, timings):
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", newline="") as csv_file:
        writer = csv.DictWriter(csv_file, fieldnames=["stage", "seconds"])
        writer.writeheader()
        for stage, seconds in sorted(timings.items()):
            writer.writerow({"stage": stage, "seconds": f"{seconds:.12g}"})


def run_one(input_path, args):
    output_dir = args.output_dir or input_path.parent
    output_path = args.output or default_output_path(
        input_path, output_dir, args.lambda_column, args.target
    )

    timings = {}

    load_start = time.perf_counter()
    rows, variable_names, lambda_start, system, start_point = load_problem(
        input_path=input_path,
        lambda_column=args.lambda_column,
        parameter_symbol=args.parameter_symbol,
        target_value=args.target,
        path_symbol=args.path_symbol,
    )
    timings["load_problem_seconds"] = time.perf_counter() - load_start

    eval_start = time.perf_counter()
    start_residual = system.eval(start_point, bertini.multiprec.Complex("1"))
    timings["start_residual_seconds"] = time.perf_counter() - eval_start

    continuation_start = time.perf_counter()
    status, endpoint, residual = continue_parameter(
        system=system,
        start_point=start_point,
        tracking_tolerance=args.tracking_tolerance,
        infinite_tolerance=args.infinite_tolerance,
        max_precision=args.max_precision,
        max_num_steps=args.max_num_steps,
        initial_step_size=args.initial_step_size,
        max_step_size=args.max_step_size,
        max_newton_iterations=args.max_newton_iterations,
        predictor=args.predictor,
    )
    timings["continuation_seconds"] = time.perf_counter() - continuation_start

    write_start = time.perf_counter()
    if args.legacy_output:
        write_legacy_result(output_path, variable_names, endpoint)
    else:
        write_result(
            output_path=output_path,
            input_path=input_path,
            rows=rows,
            variable_names=variable_names,
            lambda_column=args.lambda_column,
            parameter_symbol=args.parameter_symbol,
            lambda_start=lambda_start,
            target_value=args.target,
            start_point=start_point,
            endpoint=endpoint,
            residual=residual,
            status=status,
        )
    timings["write_output_seconds"] = time.perf_counter() - write_start
    timings["script_total_seconds"] = sum(timings.values())

    if args.timing_file:
        write_timing_file(args.timing_file, timings)

    print(f"Input: {input_path}")
    print(f"{args.lambda_column}: {lambda_start} -> {args.target}")
    print(f"parameter symbol in expressions: {args.parameter_symbol}")
    print(f"status: {status}")
    print("start residual:")
    print(start_residual)
    print("endpoint:")
    for name, value in zip(variable_names, endpoint):
        print(f"  {name} = {value}")
    print(f"residual at {args.lambda_column} = {args.target}:")
    print(residual)
    print(f"wrote: {output_path}")
    if str(status) != "Success":
        print(f"non-success Bertini status: {status}", file=sys.stderr)
        raise SystemExit(2)
    return output_path


def main():
    parser = argparse.ArgumentParser(
        description=(
            "Continue solution points stored in CSV files from one parameter value "
            "to a target value with Bertini."
        )
    )
    parser.add_argument("inputs", nargs="*", type=Path, default=[DEFAULT_INPUT])
    parser.add_argument("--output", type=Path, help="Output CSV path. Only valid for one input.")
    parser.add_argument("--output-dir", type=Path, help="Directory for generated output CSV files.")
    parser.add_argument(
        "--lambda-column",
        default="lambda0",
        help="CSV column containing the starting parameter value.",
    )
    parser.add_argument(
        "--parameter-symbol",
        default="h",
        help="Symbol used by the equations for the continuation parameter.",
    )
    parser.add_argument(
        "--target",
        default="0",
        help="Target parameter value. The default continues to 0.",
    )
    parser.add_argument(
        "--path-symbol",
        default="t",
        help="Internal Bertini path variable name.",
    )
    parser.add_argument("--tracking-tolerance", type=float, default=1e-8)
    parser.add_argument("--infinite-tolerance", type=float, default=1e8)
    parser.add_argument(
        "--default-precision",
        type=int,
        help="Set Bertini's default multiprecision digits before loading the system.",
    )
    parser.add_argument(
        "--max-precision",
        type=int,
        help="Maximum adaptive precision digits for AMPTracker.",
    )
    parser.add_argument(
        "--max-num-steps",
        type=int,
        help="Maximum number of path-tracking steps.",
    )
    parser.add_argument(
        "--initial-step-size",
        help="Initial path step size as a rational string, for example 1/100.",
    )
    parser.add_argument(
        "--max-step-size",
        help="Maximum path step size as a rational string, for example 1/100.",
    )
    parser.add_argument(
        "--max-newton-iterations",
        type=int,
        help="Maximum Newton correction iterations per tracking step.",
    )
    parser.add_argument(
        "--predictor",
        choices=sorted(bertini.tracking.Predictor.names),
        help="Tracker predictor, for example RKCashKarp45 or RKDormandPrince56.",
    )
    parser.add_argument(
        "--legacy-output",
        action="store_true",
        help="Write Julia-compatible CSV with columns var,b_final_value.",
    )
    parser.add_argument(
        "--timing-file",
        type=Path,
        help="Optional timing CSV path with columns stage,seconds.",
    )
    args = parser.parse_args()

    if args.output and len(args.inputs) != 1:
        parser.error("--output can only be used with exactly one input CSV")

    if args.default_precision is not None:
        bertini.default_precision(args.default_precision)

    for index, input_path in enumerate(args.inputs):
        if index:
            print()
        run_one(input_path, args)


if __name__ == "__main__":
    main()
