\insert 'Stack.oz'

declare
AST = [var ident(x) [var ident(y) [[var ident(x) [bind ident(x) literal(2)]] [bind ident(x) literal(3)]]]]

{SemanticStack AST}