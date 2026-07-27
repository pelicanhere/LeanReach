# Third-party notices

LeanReach's environment lifecycle, cache strategy, and command-line organization were informed by
[Loogle](https://github.com/nomeata/loogle):

> Copyright (c) 2023 Joachim Breitner and contributors  
> Released under the Apache License 2.0.

LeanReach uses Lean's public `importModules`, delaborator, declaration-range, and module-data APIs;
its cache serialization wrapper and generated-declaration filter are adapted from Loogle's
`Pickle` and `BlackListed` modules. LeanReach does not vendor Loogle's parser, trie, or matcher.
