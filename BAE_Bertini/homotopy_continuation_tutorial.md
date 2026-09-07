# A Tiny Homotopy Continuation Tutorial with Bertini 2

This tutorial uses the local virtual environment in this folder and the current
`bertini2` package, which imports as `bertini`.

The example solves the target system

```text
x^2 + y^2 - 1 = 0
x + y = 0
```

Geometrically, this asks for the intersection of the unit circle with the line
`y = -x`. The exact answers are

```text
( 1/sqrt(2), -1/sqrt(2))
(-1/sqrt(2),  1/sqrt(2))
```

Homotopy continuation solves this by creating an easier start system, then
tracking solution paths from the start system at `t = 1` to the target system at
`t = 0`.

## 1. Activate the Environment

From this folder:

```bash
source .venv/bin/activate
```

Check that Bertini imports:

```bash
python -c "import bertini; print(bertini.__version__)"
```

You should see `2.0.2` or similar.

## 2. Build the Target System

```python
import bertini

x = bertini.Variable("x")
y = bertini.Variable("y")

target = bertini.System()
variables = bertini.VariableGroup()
variables.append(x)
variables.append(y)
target.add_variable_group(variables)

target.add_function(x**2 + y**2 - 1)
target.add_function(x + y)
```

In Bertini, each function added to a system is interpreted as being equal to
zero, so `x + y` means `x + y = 0`.

## 3. Make a Total Degree Start System

```python
from bertini.system.start_system import TotalDegree

start = TotalDegree(target)

print(target.degrees())
print(start.num_start_points())
```

The degrees are `[2, 1]`, so the total-degree start system has `2 * 1 = 2`
start points. Those two start points correspond to the two paths we will track.

## 4. Build the Homotopy

```python
t = bertini.Variable("t")
homotopy = (1 - t) * target + t * start
homotopy.add_path_variable(t)
```

This creates the family

```text
H(x, y, t) = (1 - t) * target(x, y) + t * start(x, y)
```

At `t = 1`, `H` is the easy start system. At `t = 0`, `H` is the target system.

## 5. Track the Paths

```python
tracker = bertini.tracking.AMPTracker(homotopy)
tracker.tracking_tolerance(1e-8)
tracker.infinite_truncation_tolerance(1e8)

for path_number in range(start.num_start_points()):
    endpoint = bertini.multiprec.Vector(target.num_variables())
    status = tracker.track_path(
        result=endpoint,
        start_time=bertini.multiprec.Complex(1),
        end_time=bertini.multiprec.Complex(0),
        start_point=start.start_point_mp(path_number),
    )
    print(path_number, status)
    print(endpoint)
```

`AMPTracker` is Bertini's adaptive multiple-precision tracker. It starts with
ordinary precision when possible and can raise precision when the path needs it.

## 6. Run the Demo

I put the complete example in `homotopy_continuation_demo.py`. Run it with:

```bash
.venv/bin/python homotopy_continuation_demo.py
```

Typical output looks like:

```text
Target degrees: [2, 1]
Number of start paths: 2

Tracked endpoints:
path 0: Success
[(7.071067811865474620e-01, ...)
 (-7.071067811865474620e-01, ...)]
path 1: Success
[(-7.0710678118654746171500e-01, ...)
 (7.0710678118654746171500e-01, ...)]
```

The real parts are approximately `0.70710678` and `-0.70710678`, which are
`1/sqrt(2)` and `-1/sqrt(2)`.

## Notes

- Older PyBertini docs use `import pybertini`; the installed `bertini2` wheel
  uses `import bertini`.
- The historical docs describe the same basic workflow: create a system, create
  a total-degree start system, form a homotopy with a path variable, and track
  paths from `t = 1` to `t = 0`.
- In this environment, direct `System.eval` experiments across changed
  multiprecision settings were unstable, so this first tutorial keeps validation
  visual and numerical by inspecting the tracked endpoints.

## Sources

- PyBertini introduction:
  https://ofloveandhate-pybertini.readthedocs.io/en/feature-readthedocs_integration/intro.html
- PyBertini tracking tutorial:
  https://ofloveandhate-pybertini.readthedocs.io/en/feature-readthedocs_integration/tutorials/tracking_nonsingular.html
- Bertini 2 repository:
  https://github.com/bertiniteam/b2
