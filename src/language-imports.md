# Imports

## Local Import

```viper
import "path/to/local.vpr"
```

## Standard Import

```viper
import <path/to/provided.vpr>
```

Imports provide a simple mechanism for splitting a Viper program across several source files using the *local import*. Further, it also makes it possible to make use of programs provided by Viper using the *standard import*.

* A relative or absolute path to a Viper file may be used (according to the Java/Unix style)
* `import` adds the imported program as a preamble to the current one
* Transitive imports are supported and resolved via depth-first traversal of the import graph
* The depth-first traversal mechanism enforces that each Viper file is imported at most once,
  including in the cases of multiple (indirect) imports of the same file or of recursive imports.
