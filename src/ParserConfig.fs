module ParserConfig
      
let mutable private succinct = false // Default value for succinct assertions in the AST

type ParserOption =
   
   static member Succinct
      with get() = succinct
      and set(value: bool) = succinct <- value
