# SimpleFP
A series of implementations of a simple functional programming language, progressing from a very basic variant with no parametric types or polymorphism, through a parametric and polymorphic language, to a dependently typed language with various levels of user-friendliness.

The `Core` modules define the language proper. The `Monadic` modules use a monadic style for managing information. The `Unification` modules are a variant of the `Monadic` modules that use metavariables and unification instead of equality tests to allow a wider ranger of programs, especially where implicit arguments are present, as in the polymorphic variant.

You can try this out in cabal by doing `cabal repl` to load it up, then

    Simple.Monadic.REPL.replFile "src/Demos.sfp"

This starts a REPL in the SimpleFP language, by loading and compiling the specified file (here just Demos.sfp). You can then test out the functions:

    $> even Zero
    True
    
    $> odd (Suc (Suc Zero))
    False