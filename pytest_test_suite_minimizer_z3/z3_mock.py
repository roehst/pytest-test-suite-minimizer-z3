"""Mock Z3 implementation for testing the plugin without Z3 dependency."""

# Mock Z3 classes and functions for testing

class MockBool:
    def __init__(self, value):
        self.value = value
    
    def __str__(self):
        return str(self.value)


class MockBoolVar:
    def __init__(self, name):
        self.name = name
        self.value = True  # Default value
    
    def __str__(self):
        return self.name
    
    def __eq__(self, other):
        return f"({self.name} == {other})"


class MockSolver:
    def __init__(self):
        self.constraints = []
        self.stack = []
    
    def add(self, constraint):
        self.constraints.append(constraint)
    
    def push(self):
        self.stack.append(len(self.constraints))
    
    def pop(self):
        if self.stack:
            count = self.stack.pop()
            self.constraints = self.constraints[:count]
    
    def check(self):
        return "sat"
    
    def model(self):
        return MockModel()


class MockModel:
    def eval(self, var, model_completion=False):
        # Simple mock - return True for most variables to simulate coverage
        if hasattr(var, 'name'):
            var_name = var.name
        else:
            var_name = str(var)
        
        # Simulate some coverage patterns
        if any(pattern in var_name for pattern in ["test_", "example/", ":"]):
            return MockBool(True)
        return MockBool(False)


def Bool(name):
    """Mock Bool function."""
    return MockBoolVar(name)


def Implies(a, b):
    """Mock Implies function."""
    return f"({a} => {b})"


def PbEq(terms, value):
    """Mock PbEq (pseudo-boolean equals) function."""
    return f"sum({terms}) == {value}"


def is_true(val, model_completion=None):
    """Mock is_true function."""
    if hasattr(val, 'value'):
        return val.value
    return True  # Default to true for testing


def If(condition, then_val, else_val):
    """Mock If function."""
    return then_val if condition else else_val


# Mock the module
class MockZ3Module:
    @staticmethod
    def Solver():
        return MockSolver()
    
    @staticmethod
    def Bool(name):
        return MockBoolVar(name)
    
    @staticmethod
    def Implies(a, b):
        return f"({a} => {b})"
    
    @staticmethod
    def PbEq(terms, value):
        return f"sum({terms}) == {value}"
    
    @staticmethod
    def is_true(val, model_completion=None):
        if hasattr(val, 'value'):
            return val.value
        return True
    
    @staticmethod
    def If(condition, then_val, else_val):
        return then_val if condition else else_val
    
    sat = "sat"


# For when z3 is not available, we can use this mock
z3_mock = MockZ3Module()