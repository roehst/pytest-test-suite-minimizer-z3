from abc import ABC
from dataclasses import dataclass


class Term(ABC):
    pass


@dataclass
class Variable(Term):
    name: str


@dataclass
class Constant(Term):
    value: int


@dataclass
class Boolean(Term):
    value: bool


@dataclass
class If(Term):
    condition: Term
    then_branch: Term
    else_branch: Term


@dataclass
class Add(Term):
    left: Term
    right: Term


@dataclass
class Multiply(Term):
    left: Term
    right: Term


@dataclass
class Let(Term):
    var: Variable
    value: Term
    body: Term


@dataclass
class Lambda(Term):
    param: Variable
    body: Term


@dataclass
class Application(Term):
    function: Term
    argument: Term


class Value(ABC):
    pass


@dataclass
class IntValue(Value):
    value: int


@dataclass
class Closure(Value):
    param: Variable
    body: Term
    env: "Environment"


@dataclass
class BoolValue(Value):
    value: bool


@dataclass
class Environment:
    bindings: list[tuple[str, Value]]
    parent: "Environment | None"

    def extend(self, var: Variable, value: Value) -> "Environment":
        new_env: Environment = Environment(bindings=[], parent=self)
        new_env.bindings.append((var.name, value))
        return new_env

    def lookup(self, var: Variable) -> Value:
        for name, value in reversed(self.bindings):
            if name == var.name:
                return value
        if self.parent is not None:
            return self.parent.lookup(var)
        raise NameError(f"Variable '{var.name}' not found in environment.")


class Interpreter:
    def eval(self, term: Term, env: Environment) -> Value:
        if isinstance(term, Constant):
            return IntValue(term.value)
        elif isinstance(term, Boolean):
            return BoolValue(term.value)
        elif isinstance(term, Variable):
            return env.lookup(term)
        elif isinstance(term, If):
            cond_value = self.eval(term.condition, env)
            if not isinstance(cond_value, BoolValue):
                raise TypeError("Condition of If must evaluate to a Boolean.")
            if cond_value.value:
                return self.eval(term.then_branch, env)
            else:
                return self.eval(term.else_branch, env)
        elif isinstance(term, Add):
            left_value: Value = self.eval(term.left, env)
            right_value: Value = self.eval(term.right, env)
            if not isinstance(left_value, IntValue) or not isinstance(
                right_value, IntValue
            ):
                raise TypeError("Both operands of Add must evaluate to Integers.")
            return IntValue(left_value.value + right_value.value)
        elif isinstance(term, Multiply):
            left_value = self.eval(term.left, env)
            right_value = self.eval(term.right, env)
            if not isinstance(left_value, IntValue) or not isinstance(
                right_value, IntValue
            ):
                raise TypeError("Both operands of Multiply must evaluate to Integers.")
            return IntValue(left_value.value * right_value.value)
        elif isinstance(term, Let):
            value = self.eval(term.value, env)
            new_env = env.extend(term.var, value)
            return self.eval(term.body, new_env)
        elif isinstance(term, Lambda):
            return Closure(term.param, term.body, env)
        elif isinstance(term, Application):
            func_value = self.eval(term.function, env)
            arg_value = self.eval(term.argument, env)
            if not isinstance(func_value, Closure):
                raise TypeError("Function in Application must evaluate to a Closure.")
            new_env: Environment = Environment(bindings=[], parent=None)
            for name, value in func_value.env.bindings:
                new_env.bindings.append((name, value))
            new_env = new_env.extend(func_value.param, arg_value)
            return self.eval(func_value.body, new_env)
        else:
            raise TypeError(f"Unknown term type: {type(term)}")
