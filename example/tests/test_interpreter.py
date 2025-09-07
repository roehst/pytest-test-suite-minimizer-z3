from example.app.interpreter import (
    Application,
    Constant,
    IntValue,
    Interpreter,
    Lambda,
    Let,
    Multiply,
    Variable,
    Add,
    Environment,
)


def test_let1():
    interpreter = Interpreter()
    term = Let(
        var=Variable("x"), value=Constant(10), body=Add(Variable("x"), Constant(5))
    )
    result = interpreter.eval(term, Environment(bindings=[], parent=None))
    assert result == IntValue(15)


def test_let2():
    interpreter = Interpreter()
    term = Let(
        var=Variable("x"), value=Constant(10), body=Multiply(Variable("x"), Constant(5))
    )
    result = interpreter.eval(term, Environment(bindings=[], parent=None))
    assert result == IntValue(50)


def test_let3():
    interpreter = Interpreter()
    term = Let(
        var=Variable("x"),
        value=Constant(10),
        body=Let(
            var=Variable("y"),
            value=Constant(5),
            body=Add(Variable("x"), Variable("y")),
        ),
    )
    result = interpreter.eval(term, Environment(bindings=[], parent=None))
    assert result == IntValue(15)


def test_application():
    interpreter = Interpreter()
    term = Let(
        var=Variable("add"),
        value=Lambda(
            param=Variable("x"),
            body=Lambda(param=Variable("y"), body=Add(Variable("x"), Variable("y"))),
        ),
        body=Application(
            function=Application(function=Variable("add"), argument=Constant(10)),
            argument=Constant(5),
        ),
    )
    result = interpreter.eval(term, Environment(bindings=[], parent=None))
    assert result == IntValue(15)
