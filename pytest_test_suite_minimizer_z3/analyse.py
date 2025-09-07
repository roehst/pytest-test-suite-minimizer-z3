import logging

import coverage, re

data_file = ".coverage"
cov = coverage.Coverage(data_file=data_file)
cov.load()
data = cov.get_data()

total_measurable_contexts = data.measured_contexts()

byline_no = data.contexts_by_lineno

CTX_RE = re.compile(r"^test:(?P<nodeid>.+)$")

logger = logging.getLogger("analyser")
logger.setLevel(logging.DEBUG)
ch = logging.StreamHandler()
ch.setLevel(logging.DEBUG)
formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
ch.setFormatter(formatter)
logger.addHandler(ch)
debug = logger.debug

coverage = {}

total_lines = 0

for fname in data.measured_files():
    for lineno, ctxs in byline_no(fname).items():
        total_lines += 1
        for ctx in ctxs:
            if ctx not in coverage:
                coverage[ctx] = set()
            coverage[ctx].add((fname, lineno))

import z3

_contexts = {}
_coverage_points = {}

solver = z3.Solver()

for ctx, lines in coverage.items():
    if not ctx.strip():
        continue
    # create a boolean variable for this ctx; will
    # be True if this ctx is selected
    ctx_var = z3.Bool(ctx)
    _contexts[ctx] = (ctx_var, lines)
    # for each line, print it
    for line in lines:
        fname, lineno = line
        point = f"{fname}:{lineno}"
        # Create a new boolean variable for this point
        if point not in _coverage_points:
            point_var = z3.Bool(point)
            _coverage_points[point] = point_var
        else:
            point_var = _coverage_points[point]
        # Create an implication: if ctx_var is True,
        # then point_var must be True
        cov_expr = z3.Implies(ctx_var, point_var)
        solver.add(cov_expr)

# Now, we want to count how many unique points are covered
# and how many contexts are selected
total_cov = 0

for point_var in _coverage_points.values():
    total_cov += z3.If(point_var, 1, 0)

total_selected = 0
for ctx_var, _ in _contexts.values():
    total_selected += z3.If(ctx_var, 1, 0)

# We want to first:
# find maximal coverage.
# That is, push a frame, set all ctx to True, and count coverage
solver.push()
for ctx_var, _ in _contexts.values():
    solver.add(ctx_var == True)

res = solver.check()
assert res == z3.sat
model = solver.model()
max_coverage = 0
for point_var in _coverage_points.values():
    if z3.is_true(model.eval(point_var, model_completion=True)):
        max_coverage += 1
debug(f"Max coverage: {max_coverage}")
debug(f"Total measurable lines: {total_lines}")
solver.pop()

# Now, push again.
# For each test, show the coverage if onlyit is selected (Set all other to false)

for ctx_var, _ in _contexts.values():
    solver.push()
    solver.add(ctx_var == True)
    for other_ctx_var, _ in _contexts.values():
        if other_ctx_var is not ctx_var:
            solver.add(other_ctx_var == False)
    res = solver.check()
    assert res == z3.sat
    model = solver.model()
    cov = 0
    for point_var in _coverage_points.values():
        if z3.is_true(model.eval(point_var, model_completion=True)):
            cov += 1
    # _contexts[ctx_var.decl().name()][1] = cov
    debug(f"Coverage with only {ctx_var.decl().name()}: {cov}")
    solver.pop()
    # Now coverage WITHOUT
    solver.push()
    solver.add(ctx_var == False)
    for other_ctx_var, _ in _contexts.values():
        if other_ctx_var is not ctx_var:
            solver.add(other_ctx_var == True)
    res = solver.check()
    assert res == z3.sat
    model = solver.model()
    cov = 0
    for point_var in _coverage_points.values():
        if z3.is_true(model.eval(point_var, model_completion=True)):
            cov += 1
    # _contexts[ctx_var.decl().name()][1] = cov
    debug(f"Coverage without {ctx_var.decl().name()}: {cov}")
    solver.pop()

# Build a binary tree that shows the coverage for
# each possible combination of tests
# up to a certain depth

combinations = 2 ** len(_contexts)
debug(f"Total combinations: {combinations}")


def recursively_enumerate_combinations_and_yield(xs):
    if len(xs) == 0:
        yield []
    else:
        h, *t = xs
        # now, h might be True or False
        for rest in recursively_enumerate_combinations_and_yield(t):
            yield [h] + rest
            yield rest


_scores = {}

for i, combo in enumerate(
    recursively_enumerate_combinations_and_yield(list(_contexts.keys()))
):
    # activate only tests in combo
    solver.push()
    for ctx in _contexts.keys():
        ctx_var, _ = _contexts[ctx]
        if ctx in combo:
            solver.add(ctx_var == True)
        else:
            solver.add(ctx_var == False)
    res = solver.check()
    assert res == z3.sat
    model = solver.model()
    cov = 0
    for point_var in _coverage_points.values():
        if z3.is_true(model.eval(point_var, model_completion=True)):
            cov += 1
    combo_size = len(combo)
    debug(
        f"Coverage with combination {i + 1}/{combinations} ({combo}): {cov}, efficiency: {cov / (combo_size if combo_size > 0 else 1):.2f}"
    )
    _scores[tuple(sorted(combo))] = cov
    solver.pop()

_best_per_cost = {}

for combo, score in sorted(_scores.items(), key=lambda x: -x[1]):
    debug(f"{len(combo)} tests, coverage {score}: {combo}")

    if len(combo) not in _best_per_cost or _best_per_cost[len(combo)][1] < score:
        _best_per_cost[len(combo)] = (combo, score)

print("\nBest per cost:")
for cost, (combo, score) in sorted(_best_per_cost.items(), reverse=True):
    print(f"{cost} tests, coverage {score}")
    for ctx in combo:
        print(f"  - {ctx}")

# plot using terminal

print("\nCoverage per cost:")

for cost in range(0, max(_best_per_cost.keys()) + 1):
    if cost in _best_per_cost:
        combo, score = _best_per_cost[cost]
        bar_length = int((score / max_coverage) * 50)
        bar = "#" * bar_length + "-" * (50 - bar_length)
        max_cost = max(_best_per_cost.keys())
        efficiency = cost / max_cost if max_cost > 0 else 0
        print(
            f"{cost:2d} |{bar}| {score}/{max_coverage} (coverage {100 * (score - max_coverage) / max_coverage:.2f}%) efficiency: +{100 - 100 * efficiency:.2f}"
        )
