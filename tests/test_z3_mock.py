"""Test the Z3 mock functionality."""

import pytest
from pytest_test_suite_minimizer_z3.z3_mock import (
    MockBool, MockBoolVar, MockSolver, MockModel,
    Bool, Implies, PbEq, is_true, If, MockZ3Module, z3_mock
)


class TestMockBool:
    """Test the MockBool class."""
    
    def test_initialization(self):
        """Test MockBool initialization."""
        bool_true = MockBool(True)
        bool_false = MockBool(False)
        
        assert bool_true.value is True
        assert bool_false.value is False
    
    def test_string_representation(self):
        """Test MockBool string representation."""
        bool_true = MockBool(True)
        bool_false = MockBool(False)
        
        assert str(bool_true) == "True"
        assert str(bool_false) == "False"


class TestMockBoolVar:
    """Test the MockBoolVar class."""
    
    def test_initialization(self):
        """Test MockBoolVar initialization."""
        var = MockBoolVar("test_var")
        
        assert var.name == "test_var"
        assert var.value is True  # Default value
    
    def test_string_representation(self):
        """Test MockBoolVar string representation."""
        var = MockBoolVar("my_variable")
        
        assert str(var) == "my_variable"
    
    def test_equality_operation(self):
        """Test MockBoolVar equality operation."""
        var = MockBoolVar("test_var")
        
        result = var == True
        assert result == "(test_var == True)"
        
        result = var == False
        assert result == "(test_var == False)"


class TestMockSolver:
    """Test the MockSolver class."""
    
    def test_initialization(self):
        """Test MockSolver initialization."""
        solver = MockSolver()
        
        assert solver.constraints == []
        assert solver.stack == []
    
    def test_add_constraint(self):
        """Test adding constraints to solver."""
        solver = MockSolver()
        
        solver.add("constraint1")
        solver.add("constraint2")
        
        assert solver.constraints == ["constraint1", "constraint2"]
    
    def test_push_pop_operations(self):
        """Test push/pop stack operations."""
        solver = MockSolver()
        
        # Add some constraints
        solver.add("constraint1")
        solver.add("constraint2")
        
        # Push current state
        solver.push()
        assert solver.stack == [2]
        
        # Add more constraints
        solver.add("constraint3")
        solver.add("constraint4")
        assert len(solver.constraints) == 4
        
        # Pop back to previous state
        solver.pop()
        assert solver.constraints == ["constraint1", "constraint2"]
        assert solver.stack == []
    
    def test_multiple_push_pop(self):
        """Test multiple push/pop operations."""
        solver = MockSolver()
        
        solver.add("c1")
        solver.push()  # Save state with 1 constraint
        
        solver.add("c2")
        solver.push()  # Save state with 2 constraints
        
        solver.add("c3")
        assert len(solver.constraints) == 3
        
        solver.pop()  # Back to 2 constraints
        assert len(solver.constraints) == 2
        
        solver.pop()  # Back to 1 constraint
        assert len(solver.constraints) == 1
    
    def test_check_always_satisfiable(self):
        """Test that check always returns sat."""
        solver = MockSolver()
        
        assert solver.check() == "sat"
        
        # Even with constraints
        solver.add("some constraint")
        assert solver.check() == "sat"
    
    def test_model_creation(self):
        """Test model creation."""
        solver = MockSolver()
        
        model = solver.model()
        assert isinstance(model, MockModel)


class TestMockModel:
    """Test the MockModel class."""
    
    def test_eval_with_var_name(self):
        """Test evaluation with variable name."""
        model = MockModel()
        
        # Mock variable with name attribute
        var = MockBoolVar("test_variable")
        result = model.eval(var)
        
        assert isinstance(result, MockBool)
        assert result.value is True  # Should return True for test patterns
    
    def test_eval_with_test_patterns(self):
        """Test evaluation with different name patterns."""
        model = MockModel()
        
        # Test patterns that should return True
        test_patterns = [
            MockBoolVar("test_function"),
            MockBoolVar("example/module.py"),
            MockBoolVar("file.py:10"),
            MockBoolVar("test:some_test|run")
        ]
        
        for var in test_patterns:
            result = model.eval(var)
            assert result.value is True
    
    def test_eval_with_non_test_patterns(self):
        """Test evaluation with non-test patterns."""
        model = MockModel()
        
        # Patterns that should return False
        non_test_patterns = [
            MockBoolVar("simple_var"),
            MockBoolVar("other_variable")
        ]
        
        for var in non_test_patterns:
            result = model.eval(var)
            assert result.value is False
    
    def test_eval_with_string_var(self):
        """Test evaluation with string variable."""
        model = MockModel()
        
        # Should work with string variables too
        result = model.eval("test_something")
        assert isinstance(result, MockBool)


class TestMockFunctions:
    """Test the mock Z3 functions."""
    
    def test_bool_function(self):
        """Test Bool function."""
        var = Bool("test_variable")
        
        assert isinstance(var, MockBoolVar)
        assert var.name == "test_variable"
    
    def test_implies_function(self):
        """Test Implies function."""
        var_a = MockBoolVar("a")
        var_b = MockBoolVar("b")
        
        result = Implies(var_a, var_b)
        assert result == "(a => b)"
    
    def test_pbeq_function(self):
        """Test PbEq function."""
        terms = [("var1", 1), ("var2", 1)]
        
        result = PbEq(terms, 2)
        assert result == "sum([('var1', 1), ('var2', 1)]) == 2"
    
    def test_is_true_function(self):
        """Test is_true function."""
        # Test with MockBool
        bool_true = MockBool(True)
        bool_false = MockBool(False)
        
        assert is_true(bool_true) is True
        assert is_true(bool_false) is False
        
        # Test with other values (should default to True)
        assert is_true("anything") is True
        assert is_true(None) is True
    
    def test_if_function(self):
        """Test If function."""
        result_true = If(True, "then_value", "else_value")
        result_false = If(False, "then_value", "else_value")
        
        assert result_true == "then_value"
        assert result_false == "else_value"


class TestMockZ3Module:
    """Test the MockZ3Module class."""
    
    def test_solver_method(self):
        """Test Solver method."""
        module = MockZ3Module()
        
        solver = module.Solver()
        assert isinstance(solver, MockSolver)
    
    def test_bool_method(self):
        """Test Bool method."""
        module = MockZ3Module()
        
        var = module.Bool("test_var")
        assert isinstance(var, MockBoolVar)
        assert var.name == "test_var"
    
    def test_implies_method(self):
        """Test Implies method."""
        module = MockZ3Module()
        
        result = module.Implies("a", "b")
        assert result == "(a => b)"
    
    def test_pbeq_method(self):
        """Test PbEq method."""
        module = MockZ3Module()
        
        terms = [("x", 1), ("y", 1)]
        result = module.PbEq(terms, 1)
        assert result == "sum([('x', 1), ('y', 1)]) == 1"
    
    def test_is_true_method(self):
        """Test is_true method."""
        module = MockZ3Module()
        
        bool_val = MockBool(True)
        assert module.is_true(bool_val) is True
        
        bool_val = MockBool(False)
        assert module.is_true(bool_val) is False
    
    def test_if_method(self):
        """Test If method."""
        module = MockZ3Module()
        
        result = module.If(True, "yes", "no")
        assert result == "yes"
        
        result = module.If(False, "yes", "no")
        assert result == "no"
    
    def test_sat_constant(self):
        """Test sat constant."""
        module = MockZ3Module()
        
        assert module.sat == "sat"


class TestZ3MockInstance:
    """Test the z3_mock instance."""
    
    def test_z3_mock_is_instance_of_module(self):
        """Test that z3_mock is an instance of MockZ3Module."""
        assert isinstance(z3_mock, MockZ3Module)
    
    def test_z3_mock_functionality(self):
        """Test that z3_mock provides expected functionality."""
        # Test basic usage pattern similar to real Z3
        solver = z3_mock.Solver()
        var_a = z3_mock.Bool("test_a")  # Use test pattern
        var_b = z3_mock.Bool("test_b")  # Use test pattern
        
        constraint = z3_mock.Implies(var_a, var_b)
        solver.add(constraint)
        
        assert solver.check() == z3_mock.sat
        
        model = solver.model()
        result_a = model.eval(var_a)
        result_b = model.eval(var_b)
        
        assert z3_mock.is_true(result_a)
        assert z3_mock.is_true(result_b)