from enum import Enum, unique
import random
import math

@unique
class OpTag(Enum):
    variable = 1
    product = 2
    ratio = 3
    power = 4
    addition = 5

@unique
class ConstraintTag(Enum):
    eq = 1
    le = 2
    ge = 3

def size_of(expr):
    n = 1
    try:
        for x in expr:
            if type(x) == str:
                n += 1
            else:
                n += size_of(x)
    except TypeError:
        pass
    return n

def random_tag(weights, mononomial):
    if mononomial:
        tags = set([OpTag.product, OpTag.ratio, OpTag.power])
    else:
        tags = set([OpTag.product, OpTag.ratio, OpTag.power, OpTag.addition])
    if weights is None:
        r = random.random()
        x = 0
        w = 1.0 / len(tags)
        for t in tags:
            x += w
            if r <= x:
                break
        return t
    r = random.randint(0, sum(w for t, w in weights.items() if t in tags))
    x = 0
    for t, w in weights.items():
        x += w
        if r <= x:
            break
    return t

def random_split(x):
    a = random.randint(0, x)
    b = x - a
    return a, b

def is_constant(expr):
    return type(expr) in (int, float)

def tidy_posynomial(expr):
    if is_constant(expr):
        return expr
    ty = expr[0]
    body = expr[1:]
    if ty == OpTag.variable:
        return expr
    if ty == OpTag.product or ty == OpTag.addition:
        a, b = body
        if a == b:
            return a
        x = tidy_posynomial(a)
        y = tidy_posynomial(b)
        if x in (0, 1):
            return y
        if y in (0, 1):
            return x
        if is_constant(x) and is_constant(y):
            return x
        if x == y:
            if ty == OpTag.addition:
                return (OpTag.product, x, 2)
            if ty == OpTag.product:
                return (OpTag.power, x, 2)
        return (ty, x, y)
    if ty == OpTag.power:
        x, k = body
        y = tidy_posynomial(x)
        if is_constant(y):
            return y
        if y[0] == OpTag.power:
            return y
        return (ty, y, k)
    if ty == OpTag.ratio:
        a, b = body
        x = tidy_posynomial(a)
        y = tidy_posynomial(b)
        if y in (0, 1):
            return x
        if x in (0, 1):
            return y
        if is_constant(x) and is_constant(y):
            return x
        if x == y:
            return x
        return (OpTag.ratio, x, y)
    assert(False)

def random_posynomial(size, num_vars, generalized, weights=None, mononomial=False):
    while True:
        mean_exponent = random.expovariate(1.0)
        if mean_exponent < 10:
            break
    while True:
        mean_constant = random.expovariate(1.0)
        if mean_constant < 1000:
            break
    def helper(size, mononomial):
        if size <= 1:
            if random.randint(0, 1):
                var = random.randrange(0, num_vars)
                return (OpTag.variable, var)
            k = random.expovariate(mean_constant)
            if random.randint(0, 1):
                k = int(k)
            return k
        tag = random_tag(weights, mononomial)
        if tag == OpTag.addition or tag == OpTag.product:
            a, b = random_split(size - 1)
            l = helper(a, mononomial)
            r = helper(b, mononomial)
            return (tag, l, r)
        if tag == OpTag.power:
            while True:
                k = random.expovariate(mean_exponent)
                if (not generalized) or random.randint(0, 1):
                    k = int(k + 2)
                if k < 40:
                    break
            x = helper(size - 1, mononomial)
            return (OpTag.power, x, k)
        if tag == OpTag.ratio:
            a, b = random_split(size - 1)
            l = helper(a, mononomial)
            r = helper(b, True)
            return (OpTag.ratio, l, r)
        assert(False)
    expr = tidy_posynomial(helper(size, mononomial))
    return expr

def is_variable(b):
    return (not is_constant(b)) and b[0] == OpTag.variable

def is_ratio(b):
    return (not is_constant(b)) and b[0] == OpTag.ratio

def gen_variables(expr):
    if type(expr) != tuple:
        return
    if expr[0] == OpTag.variable:
        yield expr[1]
        return
    for x in expr[1:]:
        for v in variables(x):
            yield v

def variables(expr):
    return tuple(gen_variables(expr))

def count_vars(expr):
    if type(expr) != tuple:
        return 0
    if expr[0] == OpTag.variable:
        return 1
    return sum(count_vars(x) for x in expr[1:])

def tidy_constraint(constraint):
    tag = constraint[0]
    l, r = constraint[1:]
    a = tidy_posynomial(l)
    b = tidy_posynomial(r)
    if is_constant(a) and is_constant(b):
        return None
    if a == b:
        return None
    if tag == ConstraintTag.eq:
        if is_variable(a) and is_variable(b):
            return None
        for _ in range(2):
            if is_constant(a) and is_variable(b):
                return None
            if is_ratio(a):
                tag_a = a[0]
                u, v = a[1:]
                return tidy_constraint((tag, u, (OpTag.product, b, v)))
            a, b = b, a
    return (tag, l, r)

def random_constraint(size, num_vars, constraint_vars, generalized, weights=None):
    while True:
        tag = random.choice([ConstraintTag.eq, ConstraintTag.le, ConstraintTag.ge])
        size = (size - 1) // 2
        mono = random_posynomial(size, num_vars, generalized, weights, True)
        is_eq = tag == ConstraintTag.eq
        posy = random_posynomial(size, num_vars, generalized, weights, is_eq)
        if tag == ConstraintTag.le or is_eq:
            constraint = (tag, posy, mono)
        elif tag == ConstraintTag.ge:
            constraint = (tag, mono, posy)
        else:
            assert(False)
        constraint = tidy_constraint(constraint)
        new_vars = variables(constraint)
        if constraint is not None and new_vars not in constraint_vars:
            constraint_vars.add(new_vars)
            return constraint

def random_partition(n, k):
    cuts = sorted(random.sample(range(0, n + 1), k - 1))
    prev = 0
    for cut in cuts:
        yield cut - prev
        prev = cut
    yield n - prev

def random_problem(size, num_vars, generalized, weights=None, ty=None):
    assert(size > 0)
    types = ["maximization", "minimization", "feasibility"]
    if ty is None:
        ty = random.choice(types)
    else:
        assert(ty in types)
    if ty == "feasibility":
        num_constraints = random.randint(1, num_vars - 1)
        sizes = random_partition(size, num_constraints)
        result = []
        constraint_vars = set()
        for n in sizes:
            constraint = random_constraint(n, num_vars, constraint_vars, generalized, weights)
            result.append(constraint)
    else:
        if ty == "minimization":
            expression = random_posynomial(size, num_vars, generalized, weights)
        elif ty == "maximization":
            expression = random_posynomial(size, num_vars, generalized, weights, True)
        else:
            assert(False)
        expr_size, constraint_size = random_split(size)
        if constraint_size == 0:
            constraints = []
        else:
            num_constraints = random.randint(1, num_vars - 1)
            sizes = random_partition(size, num_constraints)
            constraints = []
            constraint_vars = set()
            for n in sizes:
                constraint = random_constraint(n, num_vars, constraint_vars, generalized, weights)
                constraints.append(constraint)
            constraints = constraints
        result = (constraints, tidy_posynomial(expression))
    return (ty, num_vars, result)

def name(n):
    k, a = divmod(n, 26)
    name = chr(a + ord('a'))
    if k != 0:
        name += str(int(k))
    return name

def print_posynomial(expr, prec=0, prev=None):
    if is_constant(expr):
        return str(expr)
    ty = expr[0]
    body = expr[1:]
    p = print_posynomial
    assoc = False
    if ty == OpTag.variable:
        var, = body
        result = name(var)
        new_prec = 3
    else:
        if ty == OpTag.product:
            op = "*"
            new_prec = 2
            assoc = True
        elif ty == OpTag.ratio:
            op = "/"
            new_prec = 2
        elif ty == OpTag.power:
            op = "^"
            new_prec = 2
        elif ty == OpTag.addition:
            op = "+"
            new_prec = 1
            assoc = True
        else:
            assert(False)
        a, b = body
        result = ' '.join([p(a, new_prec, ty), op, p(b, new_prec, ty)])
        assoc = ty == prev and assoc
    if new_prec < prec or ((new_prec == prec) and (not assoc)):
        result = '(' + result + ')'
    return result

def print_constraint(constraint):
    ty, l, r = constraint
    if ty == ConstraintTag.eq:
        op = "=="
    elif ty == ConstraintTag.le:
        op = "<="
    elif ty == ConstraintTag.ge:
        op = ">="
    else:
        assert(False)
    return ' '.join([print_posynomial(l), op, print_posynomial(r)])

def print_problem(problem):
    ty, num_vars, body = problem
    s = ""
    s += "cvx_begin gp\n"
    var_names = ' '.join(name(n) for n in range(num_vars))
    s += "    variables " + var_names + '\n'
    if ty in ["minimization", "maximization"]:
        constraints, objective = body
        if ty == "minimization":
            s += "    minimize"
        elif ty == "maximization":
            s += "    maximize"
        s += "( " + print_posynomial(objective) + " )\n"
    else:
        constraints = body
    s += "    subject to\n"
    for constraint in constraints:
        s += (' ' * 8) + print_constraint(constraint) + '\n'
    s += "cvx end\n"
    return s


if __name__ == "main":
    for i in range(100):
        problem = random_problem(10, 5, True)
        print(print_problem(problem))
