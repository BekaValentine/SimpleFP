# SimpleFP
A series of implementations of a simple functional programming language.

You can try this out in cabal by doing `cabal repl` to load it up, then

    Basic.REPL.replFile "src/Demos.sfp"
    
or

    Monadic.REPL.replFile "src/Demos.sfp"

This starts a REPL in the SimpleFP language, by loading and compiling the specified file (here just Demos.sfp). You can then test out the functions:

    $> even (Zero())
    True()
    
    $> odd (Suc(Suc(Zero())))
    False()

Note tho that the way the parser is set up, constructors applied to (zero or more args) need to be wrapped in parens when they're args to a function.