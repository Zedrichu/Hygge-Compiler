// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Compiler test suite.
module Test

open Expecto // See https://github.com/haf/expecto


/// Collect and sort the test files in a test directory (which is obtained by
/// combining the given paths).
let internal getFilesInTestDir paths =
    // FIXME: workaround to fix the current diretory when running 'dotnet test'
    // See: https://github.com/microsoft/vstest/issues/2004
    let dllPath = System.Reflection.Assembly.GetExecutingAssembly().Location
    let newPath = System.IO.Path.Combine(dllPath, "../../../..")
    System.IO.Directory.SetCurrentDirectory(newPath)

    let curDir = System.IO.Directory.GetCurrentDirectory()
    let dir = List.toArray(curDir :: "tests" :: paths) |> System.IO.Path.Combine
    System.IO.Directory.EnumerateFiles(dir, "*.hyg",
                                       System.IO.SearchOption.AllDirectories) |> Seq.toList |> List.sort

/// Create an easy-to-read test case name from the given file, which should
/// represent a test case under the given paths.
let internal testCaseName paths file =
    let curDir = System.IO.Directory.GetCurrentDirectory()
    let dir = List.toArray(curDir :: "tests" :: paths) |> System.IO.Path.Combine
    let relFile = System.IO.Path.GetRelativePath(dir, file)
    relFile.Remove(relFile.Length - 4) // Remove the ".hyg" extension


/// Format a bunch of type errors into a single string.
let internal formatErrors (es: Typechecker.TypeErrors): string =
    List.fold (fun acc e -> acc + (Util.formatMsg e) + Util.nl) "" es


/// Compile a source file and run the resulting assembly code on RARS, checking
/// whether its return code matches the expected one.
let internal testCodegen (file: string) (expected: int) =
    match (Util.parseFile file) with
    | Error(e) -> failwith $"Parsing failed: %s{e}"
    | Ok(ast) ->
        match (Typechecker.typecheck ast) with
        | Error(es) -> failwith $"Typing failed: %s{formatErrors es}"
        | Ok(tast) ->
            let asm = RISCVCodegen.codegen tast
            let explainExpected = RARS.explainExitCode expected
            let exit = RARS.launch (asm.ToString()) false
            let explainExit = RARS.explainExitCode exit
            Expect.equal exit expected ($"RARS should have exited with code %d{expected} (%s{explainExpected}), "
                                        + $"got %d{exit} (%s{explainExit})")


/// Compile a source file after transforming it into ANF, and run the resulting
/// assembly code on RARS, checking whether its return code matches the expected
/// one. For this test, the ANF-based compilation uses just 3 registers.
let internal testANFCodegen (file: string) (expected: int) =
    match (Util.parseFile file) with
    | Error(e) -> failwith $"Parsing failed: %s{e}"
    | Ok(ast) ->
        match (Typechecker.typecheck ast) with
        | Error(es) -> failwith $"Typing failed: %s{formatErrors es}"
        | Ok(tast) ->
            let anf = ANF.transform tast
            let asm = ANFRISCVCodegen.codegen anf 3u
            let explainExpected = RARS.explainExitCode expected
            let exit = RARS.launch (asm.ToString()) false
            let explainExit = RARS.explainExitCode exit
            Expect.equal exit expected ($"RARS should have exited with code %d{expected} (%s{explainExpected}), "
                                        + $"got %d{exit} (%s{explainExit})")


/// Return an Expecto test list for the given phase of the compiler. Note that
/// the phase name must match the name of a subdirectory of 'tests/' containing
/// 'pass/' and 'fail/' subdirectories. The given 'passTestFun' and
/// 'failTestFun' are applied to each file with extension '.hyg' found under
/// the 'pass/' and 'fail/' directories, respectively.
let internal createTestList (phase: string) (passTestFun: string -> unit)
                                            (failTestFun: string -> unit)=
    testList phase [
        testList "pass" (
            getFilesInTestDir [phase; "pass"] |> List.map ( fun file ->
                testCase (testCaseName [phase; "pass"] file) <| fun _ ->
                    passTestFun file
            )
        )
        testList "fail" (
            getFilesInTestDir [phase; "fail"] |> List.map ( fun file ->
                testCase (testCaseName [phase; "fail"] file) <| fun _ ->
                    failTestFun file
            )
        )
    ]


[<Tests>]
let tests = testList "tests" [
    createTestList "lexer"
        <| fun file ->
            Expect.isOk (Util.lexFile file) "Lexing failed"
        <| fun file ->
            Expect.isError (Util.lexFile file) "Lexing should have failed"
    createTestList "parser"
        <| fun file ->
            Expect.isOk (Util.parseFile file) "Parsing failed"
        <| fun file ->
            Expect.isError (Util.parseFile file) "Parsing should have failed"
    createTestList "typechecker"
        <| fun file ->
            match (Util.parseFile file) with
            | Error(e) -> failwith $"Parsing failed: %s{e}"
            | Ok(ast) -> Expect.isOk (Typechecker.typecheck ast) "Typing failed"
        <| fun file ->
            match (Util.parseFile file) with
            | Error(e) -> failwith $"Parsing failed: %s{e}"
            | Ok(ast) -> Expect.isError (Typechecker.typecheck ast) "Typing should have failed"
    createTestList "interpreter"
        <| fun file ->
            match (Util.parseFile file) with
            | Error(e) -> failwith $"Parsing failed: %s{e}"
            | Ok(ast) ->
                let last = Interpreter.reduceFully ast (Some (fun _ -> "")) (Some ignore)
                Expect.isFalse (Interpreter.isStuck last) "Interpreter reached a stuck expression"
        <| fun file ->
            match (Util.parseFile file) with
            | Error(e) -> failwith $"Parsing failed: %s{e}"
            | Ok(ast) ->
                let last = Interpreter.reduceFully ast (Some (fun _ -> "")) (Some ignore)
                Expect.isTrue (Interpreter.isStuck last)
                              "Interpreter should have reached a stuck expression"
    createTestList "codegen"
        <| fun file ->
            testCodegen file 0
        <| fun file ->
            testCodegen file RISCVCodegen.assertExitCode
    createTestList "codegen-anf"
        <| fun file ->
            testANFCodegen file 0
        <| fun file ->
            testANFCodegen file RISCVCodegen.assertExitCode
]


/// Run the tests according to command line options
let run (opts: CmdLine.TestOptions): int =
    let argsDebug = if opts.Verbose then ["--debug"] else []
    let argsFilter = match opts.Filter with
                     | null -> []
                     | f -> ["--filter"; $"tests.%s{f}"]
    let args = argsDebug @ argsFilter
    Expecto.Tests.runTestsWithCLIArgs [] (Array.ofList args) tests
