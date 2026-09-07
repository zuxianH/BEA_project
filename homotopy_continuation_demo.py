import bertini
from bertini.system.start_system import TotalDegree


def main():
    # Target system:
    #   x^2 + y^2 - 1 = 0
    #   x + y = 0
    #
    # Its two solutions are approximately
    #   ( 1/sqrt(2), -1/sqrt(2))
    #   (-1/sqrt(2),  1/sqrt(2))
    x = bertini.Variable("x")
    y = bertini.Variable("y")

    target = bertini.System()
    variables = bertini.VariableGroup()
    variables.append(x)
    variables.append(y)
    target.add_variable_group(variables)
    target.add_function(x**2 + y**2 - 1)
    target.add_function(x + y)

    start = TotalDegree(target)
    print("Target degrees:", list(target.degrees()))
    print("Number of start paths:", start.num_start_points())

    t = bertini.Variable("t")
    homotopy = (1 - t) * target + t * start
    homotopy.add_path_variable(t)

    tracker = bertini.tracking.AMPTracker(homotopy)
    tracker.tracking_tolerance(1e-8)
    tracker.infinite_truncation_tolerance(1e8)

    print("\nTracked endpoints:")
    for path_number in range(start.num_start_points()):
        endpoint = bertini.multiprec.Vector(target.num_variables())
        status = tracker.track_path(
            result=endpoint,
            start_time=bertini.multiprec.Complex(1),
            end_time=bertini.multiprec.Complex(0),
            start_point=start.start_point_mp(path_number),
        )
        print(f"path {path_number}: {status}")
        print(endpoint)


if __name__ == "__main__":
    main()
