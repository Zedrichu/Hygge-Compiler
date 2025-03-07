
/// Module for storing and retrieving source code content for error reporting.
module SourceRepository

/// Repository for storing source code of compiled files
type SourceRepository() =
    let mutable files = Map.empty<string, string[]>
    
    /// Add a file's content to the repository
    member this.AddFile(filename: string, content: string) =
        let lines = content.Split('\n')
        files <- files.Add(filename, lines)
    
    /// Get a specific line from a file (1-indexed)
    member this.GetLine(filename: string, lineNum: int) =
        match files.TryFind(filename) with
        | Some lines -> 
            if lineNum > 0 && lineNum <= lines.Length then
                Some lines[lineNum - 1]
            else None
        | None -> None

    member this.GetSnippet(filename: string, lineStart: int, colStart: int, lineEnd: int, colEnd: int) =
        match files.TryFind(filename) with
        | Some lines ->
            let startLine = max 0 (lineStart - 1)
            let endLine = min (lines.Length - 1) (lineEnd - 1)
            let result: string array = [| 
                for i in startLine..endLine -> 
                    let line = lines[i]
                    if i = startLine then
                        if i = endLine then
                            line.Substring(colStart - 1, colEnd - colStart + 1)
                        else
                            line.Substring(colStart - 1)
                    elif i = endLine then
                        line.Substring(0, colEnd)
                    else
                        line
            |]
            Some (result |> String.concat "\n")
        | None -> None

/// Global repository instance
let repository = SourceRepository()