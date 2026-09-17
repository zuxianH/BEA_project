"""Pre-optimization parser, retained only to reproduce the benchmark."""
import ast
from bae_bertini.continuation import normalize_mathematica_number_text, rational

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

