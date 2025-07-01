# hyggec - the Didactic Compiler for Hygge

This is the source code `hyggec`, the didactic compiler for the Hygge
programming language.

Hygge and `hyggec` have been designed and developed as learning tools for the
course *02247 Compiler Construction* at DTU Compute - Technical University of
Denmark.

`hyggec` is released under the terms of the [MIT license](LICENSE.md).

## Software Requirements

  * .NET 8.0 (for compiling and running `hyggec`): <https://dotnet.microsoft.com/en-us/download>
    - **NOTE:** if you want to use .NET 9.0 instead, you can edit the file
      `hyggec.fsproj` and set the `TargetFramework` to `net9.0`
 
  * Java Runtime Environment, at least version 17, or preferably version 21
    (for running the included copy of [RARS, the RISC-V Assembler and Runtime Simulator](https://github.com/TheThirdOne/rars))
    - On Ubuntu and Debian GNU/Linux: `sudo apt install openjdk-21-jre`
    - On MacOS: `brew install openjdk@21`
    - On Windows: <https://www.oracle.com/java/technologies/javase/jdk21-archive-downloads.html>

**NOTE:** you will need to have both the `dotnet` and `java` programs in your
[executable PATH](https://janelbrandon.medium.com/understanding-the-path-variable-6eae0936e976)
(their installation scripts should take care of it).

## Quick Start

After installing the required software above, open a terminal in the root
directory of the `hyggec` source tree, and try:

```
./hyggec test
```

This command automatically builds `hyggec` and runs its test suite. If you don't
see any error, then `hyggec` was built correctly and passed all its tests.  You
should now be able to use and modify it.

To see the usage options, you can execute:

```
./hyggec help
```

You will see a list of various commands.  To get usage options for a specific
command (for example, `compile`):

```
./hyggec compile --help
```

Here's something you can try:

```
./hyggec interpret --typecheck --verbose examples/hygge0-spec-example.hyg
```

## Building `hyggec` from the Command Line

Every time you invoke the script `./hyggec`, the compiler will be rebuilt if its
source code was modified since the last execution.

You can also (re)build the `hyggec` executable by running:

```
dotnet build
```

To clean up the results of a build, you can run:

```
dotnet clean
```

## Recommended Visual Studio Code Extensions

The following VS Code extensions is highly recommended for working on `hyggec`
(and F# projects in general):

  * [Ionide for F#](https://marketplace.visualstudio.com/items?itemName=Ionide.Ionide-fsharp)

For working on `.fsl` and `.fsy` files, you may install one of the following
extensions:

  * [FSharp fsl and fsy](https://marketplace.visualstudio.com/items?itemName=mnxn.fsharp-fsl-fsy), or
  * [FsYacc Language Service](https://marketplace.visualstudio.com/items?itemName=ijklam.fsyacc-language-service)
    (**NOTE:** this extension _might_ need the .NET 6.0 runtime installed, which
    may be problematic on some operating systems)

## License Notice

  Hygge Compiler - Compiler implementation for the didactic language Hygge <br>
  Copyright (C) 2025 Technical University of Denmark

  Authors: 
  - Adrian Zvizdenco <s204683@dtu.dk>
  - Kornel Gładkowski
  - Mikolaj Jochim
  - Simão Teixeira
  - William Brøchner Søndergaard

  This program is free software: you can redistribute it and/or modify it
  under the terms of the GNU Affero General Public License as published
  by the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU Affero General Public License for more details.

----------------------------------------------------------------------------------

Copyright (C) 2023-2025 Technical University of Denmark

Author: Alceste Scalas <alcsc@dtu.dk>

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

----------------------------------------------------------------------------------
#### Project completed in course 02267 Software Development of Web Services @ Technical University of Denmark 
<img src="https://user-images.githubusercontent.com/65953954/120001846-7f05f180-bfd4-11eb-8c11-2379a547dc9f.jpg" alt="drawing" width="100"/>

