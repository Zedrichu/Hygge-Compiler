
/// Module for storing and retrieving source code content for error reporting.
module SourceRepository

open AST

/// Repository for storing source code of compiled files
type SourceRepository() =
    let mutable files = Map.empty<string, string[]>

    member this.AddFileIntepreter(path: string) =
        this.AddFile(path, false)

    member this.AddFileAsm(path: string) =
        this.AddFile(path, true)

    /// Add a file's content to the repository
    member _.AddFile(path: string, escapeBackslash: bool) =
        let mutable lines = 
            System.IO.File.ReadAllLines(path)

        if escapeBackslash then
            lines <- Array.map (fun (line: string) -> 
            line.Replace(@"\", @"\\").Replace("\"", "\\\"")) lines

        files <- files.Add(path, lines)

    /// Get a specific line from a file (1-indexed)
    member _.GetLine(filename: string, lineNum: int) =
        files
        |> Map.tryFind filename
        |> Option.bind (fun lines ->
            if lineNum > 0 && lineNum <= lines.Length then
                Some lines.[lineNum - 1]
            else None)

    member _.GetSnippet(
        pos: AST.Position,
        markerPos: AST.Position,
        // filename: string, lineStart: int, lineEnd: int, ?colStartArg: int,
        fullLines: bool, includeLineNumbers: bool, includeMarkerLine: bool) =
        let filename = pos.FileName
        let lineStart = pos.LineStart
        let lineEnd = pos.LineEnd

        // let includeMarkerLine = defaultArg includeMarkerLine false
        // let includeLineNumbers = defaultArg includeLineNumbers false
        // let colStart =
        //     match includeMarkerLine, colStartArg with
        //     | true, None -> failwith "colStart must be provided when includeMarkerLine is true"
        //     | _, Some col -> col
        //     | false, None -> 1 // Default value when not including marker line

        // let markerPosition = defaultArg markerPosition (lineStart, colStart)
        let markerPosition = markerPos.LineStart, markerPos.ColStart

        match files.TryFind(filename) with
        | Some lines ->
            let startLine = max 0 (lineStart - 1)
            let endLine = min (lines.Length - 1) (lineEnd - 1)

            // Determine the maximum width needed for line numbers
            let maxLineNumWidth =
                if includeLineNumbers then
                    max ((endLine + 1).ToString().Length) 3 // Ensure width also works for "..."
                else 0

            
            let mutable result = 
                match fullLines with
                | true -> [ for i in startLine..endLine ->
                            let line = lines[i]

                            if includeLineNumbers then
                                let lineNum = (i + 1).ToString().PadLeft(maxLineNumWidth)
                                $"%s{lineNum}: %s{line}"
                            else
                                line ]
                | _ -> 
                    let colStart = pos.ColStart - 1 // Adjust for 0-based index
                    let colEnd = pos.ColEnd - 1     // Adjust for 0-based index
                    match (endLine - startLine) with
                    | 0 -> [lines[startLine][colStart..colEnd]]
                    | _ -> 
                        [lines[startLine][colStart..]] @
                        [ for i in (startLine+1)..(endLine-1) ->
                            let line = lines[i]

                            if includeLineNumbers then
                                let lineNum = (i + 1).ToString().PadLeft(maxLineNumWidth)
                                $"%s{lineNum}: %s{line}"
                            else
                                line ] @
                        [lines[endLine][0..colEnd]]

            if includeMarkerLine then
                // Create the marker line with '^' at colStart position
                let markerLine =
                    if includeLineNumbers then
                        let placeholder = "...".PadLeft(maxLineNumWidth)
                        let padding = String.replicate (snd markerPosition - 1) " "
                        $"%s{placeholder}: %s{padding}^"
                    else
                        let padding = String.replicate (snd markerPosition - 1) " "
                        $"%s{padding}^"

                // Insert marker line after the first line
                result <-
                    if result.Length > 0 then
                        result[0..(fst markerPosition - lineStart)] @ [markerLine] @ result[(fst markerPosition - lineStart + 1)..]
                    else result

            Some result
        | None -> None

/// Global repository instance
let repository = SourceRepository()
