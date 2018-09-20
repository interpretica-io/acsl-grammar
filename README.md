# acsl-grammar
ACSL grammar built up from official specification, with C grammar behind. For use in static analyzers.

You can compile it to whatever target you want using antlr4 targets. We use it for C++ target.
```
antlr4 -Dlanguage=CSharp ACSL.g4
```

## Completeness and modifications.
Not all functionality from ACSL grammar is supported. Pull requests are welcome!

Little modification has been applied to ACSL:
 - Support of acsl_comment

Little modification has been applied to C:
 - Don't process ACSL-style comments as regular comments

## License
 - C grammar belongs to ANTLR grammars collection: https://github.com/antlr/grammars-v4/blob/master/c/C.g4. BSD license.
 - ACSL grammar specification belongs to its original authors: https://github.com/acsl-language/acsl. CC BY 4.0

Licenses are included in LICENSE file.
