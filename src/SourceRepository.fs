
/// Module for storing and retrieving source code content for error reporting.
module SourceRepository

/// Repository for storing source code of compiled files
type SourceRepository() =
    let mutable files = Map.empty<string, string[]>

    /// Add a file's content to the repository
    member this.AddFile(path: string, content: string) =
        let lines = content.Split('\n')
        files <- Map.add path lines files

    /// Get a specific line from a file (1-indexed)
    member this.GetLine(filename: string, lineNum: int) =
        files
        |> Map.tryFind filename
        |> Option.bind (fun lines ->
            if lineNum > 0 && lineNum <= lines.Length then
                Some lines.[lineNum - 1]
            else None)

    member this.GetSnippet(
        filename: string, lineStart: int, lineEnd: int, ?colStartArg: int,
        ?includeLineNumbers: bool, ?includeMarkerLine: bool) =

        let includeMarkerLine = defaultArg includeMarkerLine false
        let includeLineNumbers = defaultArg includeLineNumbers false
        let colStart =
            match includeMarkerLine, colStartArg with
            | true, None -> failwith "colStart must be provided when includeMarkerLine is true"
            | _, Some col -> col
            | false, None -> 1 // Default value when not including marker line

        match files.TryFind(filename) with
        | Some lines ->
            let startLine = max 0 (lineStart - 1)
            let endLine = min (lines.Length - 1) (lineEnd - 1)

            // Determine the maximum width needed for line numbers
            let maxLineNumWidth =
                if includeLineNumbers then
                    max ((endLine + 1).ToString().Length) 3 // Ensure width also works for "..."
                else 0

            // Generate normal lines
            let mutable result = [
                for i in startLine..endLine ->
                    let line = lines[i]

                    if includeLineNumbers then
                        let lineNum = (i + 1).ToString().PadLeft(maxLineNumWidth)
                        $"%s{lineNum}: %s{line}"
                    else
                        line
            ]

            if includeMarkerLine then
                // Create the marker line with '^' at colStart position
                let markerLine =
                    if includeLineNumbers then
                        let placeholder = "...".PadLeft(maxLineNumWidth)
                        let padding = String.replicate (colStart - 1) " "
                        $"%s{placeholder}: %s{padding}^"
                    else
                        let padding = String.replicate (colStart - 1) " "
                        $"%s{padding}^"

                // Insert marker line after the first line
                result <-
                    if result.Length > 0 then
                        [result[0]; markerLine] @ result[1..]
                    else result

            Some result
        | None -> None

/// Global repository instance
let repository = SourceRepository()
