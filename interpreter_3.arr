use context essentials2021
### Omar I. Godinez

import s-exp as S
import lists as L
include from S: is-s-list, is-s-sym end

## ************** CORE DATA TYPES ********************

## A Library is a collection of Function Definitions 
type LibExt = List<FunDefExt>
mt-libExt = empty # use empty in a cases expr., not mt-libExt

type LibC = List<FunDefC>
mt-libC = empty # use empty in a cases expr., not mt-libC

## A "Program" Type
## Program is compirsed of a library of functions (lib)
## and source code (src)
data Program:
  | progExt(lib :: LibExt , src :: ExprExt)
  | progC(lib :: LibC, src :: ExprC)      
end

## Function Definition Types (Extended and Core)
data FunDefExt:
  | fdExt(name :: String, args :: List<String>, body :: ExprExt)
end

data FunDefC:
  | fdC(name :: String, args :: List<String>, body :: ExprC)
end

data CaseStmt: ## Special function to define a Case Statement
  | quesStmt(q :: ExprExt, e :: ExprExt)
  | elseStmt(e :: ExprExt)
end

data Binding: ## Expresions requaried to bind parameters
  | ExtBind(arg :: String, val :: ExprExt)
  | CBind(name :: String, val :: ExprC)
  | bind(name :: String, val) 
end

type Environment = List<Binding> ##Enviroment type, required to save all binding parameters
mt-env = empty
xtnd-env = link

## Extended Language Expressions 
data ExprExt:
    # Value espressions
  | trueExt
  | falseExt
  | numExt(n :: Number)
    # Binary Arithmetic expressions
  | plusExt(l :: ExprExt, r :: ExprExt)
  | subExt(l :: ExprExt, r :: ExprExt)
  | multExt(l :: ExprExt, r :: ExprExt)
  | divExt(l :: ExprExt, r :: ExprExt)
  | moduloExt(l :: ExprExt, r :: ExprExt)
    # Numeric Comparison expressions
  | equalExt(l :: ExprExt, r :: ExprExt)
  | biggerExt(l :: ExprExt, r :: ExprExt)
  | smallerExt(l :: ExprExt, r :: ExprExt)
  | biggerQExt(l :: ExprExt, r :: ExprExt)
  | smallerQExt(l :: ExprExt, r :: ExprExt)
    # Boolean Operators expressions
  | notExt(e :: ExprExt)
  | andExt(l :: ExprExt, r :: ExprExt) 
  | orExt(l :: ExprExt, r :: ExprExt)
    # Conditionals
  | ifExt(c :: ExprExt, t :: ExprExt, e :: ExprExt)
  | condExt(cnds :: List<CaseStmt>)
    # Binding expresions
  | letExt(e :: String, value :: ExprExt, body :: ExprExt) 
  | letStarExt(bindings :: List<Binding>, body :: ExprExt)
    # Lambda expresions
  | lambdaExt(arg :: List<ExprExt>, body :: ExprExt) 
  | lambAppExt(func :: ExprExt, args :: List<ExprExt>)
    # Function expresions
  | appExt(name :: String, args :: List<ExprExt>)
  | idExt(s :: String)
end

## Core Language Expressions
data ExprC:
    # Value espressions
  | trueC
  | falseC
  | numC(n :: Number)              
    # Binary Arithmetic expressions
  | plusC(l :: ExprC, r :: ExprC)  
  | multC(l :: ExprC, r :: ExprC)  
  | divC(l :: ExprC, r :: ExprC)   
  | modC(l :: ExprC, r :: ExprC)   
    # Boolean Operators expressions
  | equalC(l :: ExprC, r :: ExprC)
  | biggerC(l :: ExprC, r :: ExprC)
  | smallerC(l :: ExprC, r :: ExprC)
    # Boolean Operators expressions
  | notC(e :: ExprC)
  | andC(argl :: ExprC, argr :: ExprC)
  | orC(argl :: ExprC, argr :: ExprC)
    # Conditionals
  | ifC(c :: ExprC, t :: ExprC, e :: ExprC)
    # Binding expresions
  | letC(e :: String, value :: ExprC, body :: ExprC)
  | letStarC(bindings :: List<Binding>, body :: ExprC)
    # Lambda expresions
  | lambdaC(args :: List<ExprC>, body :: ExprC)
  | lambAppC(func :: ExprC, args :: List<ExprC>)
    # Function expresions
  | appC(name :: String, args :: List<ExprC>)
  | idC(s :: String)
end

## ************** PARSERS ********************

## Main parse function, gets a syntaxis expresion and returns an ExtProgram
fun parse-prog(prog :: S.S-Exp) -> Program%(is-progExt):
  cases (S.S-Exp) prog:
    | s-list(s) =>
      len = s.length()
      ask:
        | len == 0 then: raise("Parse: recive an empty list")
        | len == 1 then: progExt(mt-libExt, parse(s.get(0)))## When length is 1, it means that there is not a function definition
        | otherwise:## If there is more than one argument, then there are function definitions
          rest = parse-prog(S.s-list(s.drop(1))) ## Recursion is requaried to compute the rest of the expresion and make a library
          progExt(link(parse-def(s.get(0)), rest.lib), rest.src)## Calls parse-def to create a library and returns a progExt expresion.
      end
    | else => raise("Malformed program (need list of functions then single expression)")
  end
where:
  parse-prog(S.read-s-exp("((def (foo x) (lambda (y) (+ x y))) ((foo 42) 3))")) is progExt([list: fdExt("foo", [list: "x"], lambdaExt([list: idExt("y")], plusExt(idExt("x"), idExt("y"))))], lambAppExt(appExt("foo", [list: numExt(42)]), [list: numExt(3)]))
  parse-prog(S.read-s-exp("((and true true))")) is progExt(mt-libExt, andExt(trueExt, trueExt))
  parse-prog(S.read-s-exp("((def (f) true) (f))")) is progExt([list: fdExt("f", empty, trueExt)], appExt("f", empty))
  parse-prog(S.read-s-exp("((def (f x) (not x)) (f false))")) is progExt([list: fdExt("f", [list: "x"], notExt(idExt("x")))], appExt("f", [list: falseExt]))
  parse-prog(S.read-s-exp("((let* ((x 5) (y 42)) (+ x y)))")) is progExt([list: ], letStarExt([list: ExtBind("x", numExt(5)), ExtBind("y", numExt(42))], plusExt(idExt("x"), idExt("y"))))
  parse-prog(S.read-s-exp("((def (foo x) (lambda (y) (lambda (z) (+ x (+ y z))))) (((foo 42) 3)5))")) is progExt([list: fdExt("foo", [list: "x"], lambdaExt([list: idExt("y")], lambdaExt([list: idExt("z")], plusExt(idExt("x"), plusExt(idExt("y"), idExt("z"))))))], lambAppExt(lambAppExt(appExt("foo", [list: numExt(42)]), [list: numExt(3)]), [list: numExt(5)]))
end

fun parse-def(adef :: S.S-Exp) -> FunDefExt: ## Creates a funtion definition
  cases (S.S-Exp) adef:
    | s-list(s) => cases (List) s:
        | empty => raise("parse-def: Unexpected empty list.")
        | link(op, rest) =>
          if (op.s == "def") and (rest.length() == 2): ## The first element of a function must be a def
            block:
              sig = rest.get(0)
              when not(is-s-list(sig)): ## The second element must be a list with the function name and parameters
                raise("parse-def: Invalid function definition syntax")
              end
              name = sig.exps.get(0)    ## Gets the name
              when not(is-s-sym(name)): ## The name must be a string
                raise("parse-def: Invalid value for function name")
              end
              params = sig.exps.drop(1).map(check_string) # Makes a list with the parameters
              body = rest.get(1) # Gets the body
              fdExt(name.s, params, parse(body)) # Transforms the body into an ExprExt and returns a function definition whit all the elements
            end
          else:
            raise("parse-def: not a function definition: " + torepr(adef))
          end
      end
    | else => raise("parse-def: Not a valid function definition" + torepr(adef))
  end
where:
  parse-def(S.read-s-exp("(def (f) true)")) is fdExt("f", empty, trueExt)
  parse-def(S.read-s-exp("(def (f x) (not x))")) is fdExt("f", [list: "x"], notExt(idExt("x")))
  parse-def(S.read-s-exp("(def (main x y) (and x y))")) is fdExt("main", [list: "x", "y"], andExt(idExt("x"), idExt("y")))
end

fun parse(expr :: S.S-Exp) -> ExprExt: ## This functions is the first filter to transform the syntax expresion to an ExprExt
  cases (S.S-Exp) expr:
    | s-num(n) => numExt(n) ## Captures numbers
    | s-list(s) => ## In case of a list, it means we have a more complex expresion
      cases (List) s:
        | empty => raise("parse: unexpected empty list") ## It cannot be empty
        | link(op, args) => ## Separets the operator from the rest
          if is-s-list(op): ## If the op is a list, it should be a labda application
            lambAppExt(parse(op), args.map(parse))
          else if not(is-s-sym(op)): ## op must be a string 
            raise("parse: Invalid type in operator position")
          else if op.s == "def":     ## And different from "def"
            raise("parse: Unexpected function definition")
          else:
            parse-operation(op.s, args)## Calls parse-operation with the operator and arguments
          end
      end
    | s-sym(s) => ## When it is a string it can be true, false, or an ID
      if s == "false":
        falseExt
      else if s == "true":
        trueExt
      else:
        idExt(s)
      end
    | else => raise("parse: not a num, list, or symbol")
  end
where:
  parse(S.read-s-exp("false")) is falseExt
  parse(S.read-s-exp("true")) is trueExt
  parse(S.read-s-exp("(def (main x) x)")) raises "Unexpected function"
  parse(S.read-s-exp("x")) is idExt("x")
  parse(S.read-s-exp("(and false true)")) is andExt(falseExt, trueExt)
  parse(S.read-s-exp("(if false true false)")) is ifExt(falseExt, trueExt, falseExt)
end

fun check_string(param :: S.S-Exp) -> String: ## Small function used to verify and transform strings
  if not(is-s-sym(param)):
    raise("check_string: Function parameter is not a string")
  else:
    param.s
  end
end  

fun parse-operation(op :: String, args :: List<S.S-Exp>) -> ExprExt:## Puts together the operator and arguments to create an ExprExt
  ask: ## Identifies the operator and returns the expresion in ExprExt
      ##************Unary***********
    | op == "not" then: 
      if not(args.length() == 1):## Verify there is only one argument, because "not" is unary
        raise("parse-operation: Wrong number of arguments to not expression: " + torepr(args))
      else:
        notExt(parse(args.get(0)))## Calls parse whit the argument to compute it
      end
      ##***************Binary**********
      ## In case op is a binaty operation calls parse-binary to handel it.
    | op == "+" then: parse-binary(plusExt, args)
    | op == "-" then: parse-binary(subExt, args)
    | op == "*" then: parse-binary(multExt, args)
    | op == "/" then: parse-binary(divExt, args)
    | op == "%" then: parse-binary(moduloExt, args)
    | op == "==" then: parse-binary(equalExt, args)
    | op == ">" then: parse-binary(biggerExt, args)
    | op == "<" then: parse-binary(smallerExt, args)
    | op == ">=" then: parse-binary(biggerQExt, args)
    | op == "<=" then: parse-binary(smallerQExt, args)
    | op == "and" then: parse-binary(andExt, args)
    | op == "or" then: parse-binary(orExt, args)
      ##***************Rest*************
    | op == "let" then: letExt((((args.get(0)).exps).get(0)).s, parse(((args.get(0)).exps).get(1)), parse(args.get(1)))
    | op == "let*" then: letStarExt((args.get(0)).exps.map(binding-let),parse(args.get(1)))
    | op == "lambda" then: lambdaExt((args.get(0)).exps.map(parse), parse(args.get(1)))
    | op == "if" then:
      if args.length() == 3: ## Verify there are three argument
        ifExt(parse(args.get(0)), parse(args.get(1)), parse(args.get(2)))
      else:
        raise("parse-operation: Wrong number of arguments to if expression")
      end
    | op == "cond" then: condExt(parse-cond(args))## "cond" requires a special treatment
    | otherwise: appExt(op, args.map(parse))
  end
where:
  parse-operation("not", S.read-s-exp("(true)").exps) is notExt(trueExt)
  parse-operation("lambda", S.read-s-exp("((y) (+ x y))").exps) is lambdaExt([list: idExt("y")], plusExt(idExt("x"), idExt("y")))
  parse-operation("let", S.read-s-exp("((x 42) (+ x 1))").exps) is letExt("x", numExt(42), plusExt(idExt("x"), numExt(1)))
  parse-operation("let*", S.read-s-exp("(((x 5) (y 42)) (+ x y))").exps) is letStarExt([list: ExtBind("x", numExt(5)), ExtBind("y", numExt(42))], plusExt(idExt("x"), idExt("y")))
  parse-operation("foo", S.read-s-exp("(true)").exps) is appExt("foo", [list: trueExt])
  parse-operation("and", S.read-s-exp("(false)").exps) raises "Wrong number of arguments"
  parse-operation("and", S.read-s-exp("(false true)").exps) is andExt(falseExt, trueExt)
  parse-operation("==", S.read-s-exp("(5 5)").exps) is equalExt(numExt(5), numExt(5))
  parse-operation("if", S.read-s-exp("((and true true) true false)").exps) is ifExt(andExt(trueExt, trueExt), trueExt, falseExt)
  parse-operation("+", S.read-s-exp("(3 7)").exps) is plusExt(numExt(3), numExt(7))
end
  
fun binding-let(args :: S.S-Exp) -> Binding: ## Binds all variables in let statements
  cases (S.S-Exp) args:
    | s-list(s) => ## Checks is a list 
      ExtBind(s.get(0).s, parse(s.get(1))) ## Bind the parameter with the value
    | else => raise("parse: not a num, list, or symbol")
  end
end

fun parse-binary(op :: (ExprExt -> ExprExt), args :: List<S.S-Exp>) -> ExprExt:## Handels binary expresions
  if args.length() == 2: ## Checks it has two arguments
    op(parse(args.get(0)), parse(args.get(1))) ## Returns the operation as a ExprExt
  else:
    raise("parse-binary: Wrong number of arguments to operator: " + torepr(args))
  end
where:
  parse-binary(orExt, S.read-s-exp("()").exps) raises "Wrong number of arguments"
  parse-binary(andExt, S.read-s-exp("(true)").exps) raises "Wrong number of arguments"
  parse-binary(andExt, S.read-s-exp("(false true)").exps) is andExt(falseExt, trueExt)
  parse-binary(orExt, S.read-s-exp("(false true)").exps) is orExt(falseExt, trueExt)
  parse-binary(equalExt, S.read-s-exp("(5 5)").exps) is equalExt(numExt(5), numExt(5))
end

fun parse-cond(cnds :: List<S.S-Exp>) -> List<CaseStmt>:
  cases (List) cnds:
    | empty => empty
    | link(f,r) =>
      if not(is-s-list(f)):
        raise("parse-cond: Cond needs a list of case/else statements")
      else:
        cases (List) f.exps:
          | empty => raise("parse-cond: Unexpected empty list for case statement")
          | link(ff,fr) =>
            if not(is-s-sym(ff)):
              raise("parse-cond: Case statement must start with 'case' or 'else'")
            else if ff.s == "case":
              if not(fr.length() == 2):
                raise("parse-cond: Case statement needs condition and body expression")
              else if r.length() == 0:
                raise("parse-cond: Cond must end with an else statement")
              else:
                link(quesStmt(parse(fr.get(0)), parse(fr.get(1))), parse-cond(r))
              end
            else if ff.s == "else":
              if not(fr.length() == 1):
                raise("parse-cond: Cond else must have exactly 1 expression")
              else if r.length() > 0:
                raise("parse-cond: Case statements not allowed after else statement")
              else:
                [list: elseStmt(parse(fr.get(0)))]
              end
            else:
              raise("parse-cond: Need either 'case' or 'else' in first position of case expression")
            end
        end
      end
  end
where:
  fun p(s): parse-cond(S.read-s-exp(s).exps) end
  p("((case (not a) x) (case b (and y z)) (case (or c d) (not w)))") raises
  "parse-cond"
  p("((case (not a) x) (case b (and y z)) (else (not z)))") is
  [list: quesStmt(notExt(idExt("a")), idExt("x")),
    quesStmt(idExt("b"), andExt(idExt("y"), idExt("z"))),
    elseStmt(notExt(idExt("z")))]
  p("((case (not a) x) (else (and y z)) (case (or c d) (not w)))") raises "parse-cond"
end   

## ************** DESUGARERS ****************

## Desugar an Extended Langauge Program to the Core Language
fun desugar-prog(prog :: Program%(is-progExt)) -> Program:
  progC(prog.lib.map(desugar-def), desugar(prog.src))
where:
  desugar-prog(progExt([list: fdExt("foo", [list: "x"], lambdaExt([list: idExt("y")], plusExt(idExt("x"), idExt("y"))))], lambAppExt(appExt("foo", [list: numExt(42)]), [list: numExt(3)]))) is progC([list: fdC("foo", [list: "x"], lambdaC([list: idC("y")], plusC(idC("x"), idC("y"))))], lambAppC(appC("foo", [list: numC(42)]), [list: numC(3)]))
  desugar-prog(progExt(mt-libExt, andExt(trueExt, trueExt))) is progC(mt-libC, andC(trueC, trueC))
  desugar-prog(progExt([list: fdExt("f", empty, trueExt)], appExt("f", empty))) is progC([list: fdC("f", [list: ], trueC)], appC("f", empty))
  desugar-prog(progExt([list: fdExt("f", [list: "x"], notExt(idExt("x")))], appExt("f", [list: falseExt]))) is progC([list: fdC("f", [list: "x"], notC(idC("x")))], appC("f", [list: falseC]))
  desugar-prog(progExt([list: ], letStarExt([list: ExtBind("x", numExt(5)), ExtBind("y", numExt(42))], plusExt(idExt("x"), idExt("y"))))) is progC(empty, letStarC([list: CBind("x", numC(5)), CBind("y", numC(42))], plusC(idC("x"), idC("y"))))
  desugar-prog(progExt([list: fdExt("foo", [list: "x"], lambdaExt([list: idExt("y")], plusExt(idExt("x"), idExt("y"))))], lambAppExt(appExt("foo", [list: numExt(42)]), [list: numExt(3)]))) is progC([list: fdC("foo", [list: "x"], lambdaC([list: idC("y")], plusC(idC("x"), idC("y"))))], lambAppC(appC("foo", [list: numC(42)]), [list: numC(3)]))
  desugar-prog(progExt([list: fdExt("foo", [list: "x"], lambdaExt([list: idExt("y")], lambdaExt([list: idExt("z")], plusExt(idExt("x"), plusExt(idExt("y"), idExt("z"))))))], lambAppExt(lambAppExt(appExt("foo", [list: numExt(42)]), [list: numExt(3)]), [list: numExt(5)]))) is progC([list: fdC("foo", [list: "x"], lambdaC([list: idC("y")], lambdaC([list: idC("z")], plusC(idC("x"), plusC(idC("y"), idC("z"))))))], lambAppC(lambAppC(appC("foo", [list: numC(42)]), [list: numC(3)]), [list: numC(5)]))
end

## Desugar a Function Definition
fun desugar-def(def :: FunDefExt) -> FunDefC:
  fdC(def.name, def.args, desugar(def.body))
where:
  desugar-def(fdExt("f", [list: "x"], notExt(idExt("x")))) is fdC("f", [list: "x"], notC(idC("x")))
end

fun desugar(expr :: ExprExt) -> ExprC: ## Desugar all extended expresions
  cases (ExprExt) expr:
    | trueExt => trueC
    | falseExt => falseC
    | numExt(n) => numC(n)
    | plusExt(l, r) => plusC(desugar(l), desugar(r))
    | subExt(l, r) => plusC(desugar(l), multC(numC(-1), desugar(r)))
    | multExt(l, r) => multC(desugar(l), desugar(r))
    | divExt(l, r) => divC(desugar(l), desugar(r))
    | moduloExt(l , r) => modC(desugar(l), desugar(r))
    | equalExt(l, r) => equalC(desugar(l), desugar(r))
    | biggerExt(l, r) => biggerC(desugar(l), desugar(r))
    | smallerExt(l, r) => smallerC(desugar(l), desugar(r))
    | biggerQExt(l, r) => orC(biggerC(desugar(l), desugar(r)), equalC(desugar(l), desugar(r)))
    | smallerQExt(l, r) => orC(smallerC(desugar(l), desugar(r)), equalC(desugar(l), desugar(r)))
    | notExt(e) => notC(desugar(e))
    | andExt(l, r) => andC(desugar(l), desugar(r))
    | orExt(l, r) => orC(desugar(l), desugar(r))
    | letExt(e, v, b) => letC(e, desugar(v), desugar(b))
    | letStarExt(args, b) => letStarC(args.map(desugar-bind), desugar(b)) 
    | lambdaExt(args, b) => lambdaC(args.map(desugar), desugar(b))
    | lambAppExt(f, args) => lambAppC(desugar(f), args.map(desugar))
    | idExt(s) => idC(s)
    | appExt(n,a) => appC(n, a.map(desugar))
    | ifExt(c,t,e) => ifC(desugar(c), desugar(t), desugar(e))
    | condExt(c) => desugar-cond(c)
    | else => raise("desugar: Unexpected expression")
  end
where:
  desugar(notExt(trueExt)) is notC(trueC)
  desugar(letExt("x", trueExt, ifExt(idExt("x"), trueExt, falseExt))) is letC("x", trueC, ifC(idC("x"), trueC, falseC))
  desugar(lambdaExt([list: idExt("y")], plusExt(idExt("x"), idExt("y")))) is lambdaC([list: idC("y")], plusC(idC("x"), idC("y")))
  desugar(lambAppExt(appExt("foo", [list: numExt(42)]), [list: numExt(3)])) is lambAppC(appC("foo", [list: numC(42)]), [list: numC(3)])
  desugar(equalExt(numExt(4), numExt(2))) is equalC(numC(4), numC(2))
  desugar(andExt(trueExt, falseExt)) is andC(trueC,falseC)
  desugar(idExt("foo")) is idC("foo")
  desugar(appExt("foo", 
      [list: trueExt, notExt(falseExt), andExt(trueExt, falseExt)])) is
  appC("foo", [list: trueC, notC(falseC), andC(trueC, falseC)])
  desugar(letStarExt([list: ExtBind("x", numExt(5)), ExtBind("y", numExt(42))], plusExt(idExt("x"), idExt("y")))) is letStarC([list: CBind("x", numC(5)), CBind("y", numC(42))], plusC(idC("x"), idC("y")))
  cnds = [list: quesStmt(notExt(idExt("a")), idExt("x")),
    quesStmt(idExt("b"), andExt(idExt("y"), idExt("z"))),
    elseStmt(notExt(idExt("w")))]
  desugar(condExt(cnds)) is ifC(notC(idC("a")), idC("x"),
    ifC(idC("b"), andC(idC("y"),idC("z")), notC(idC("w"))))
end

## Especial function that structures binary C expresions
fun desugar-bind(arg :: Binding%(is-ExtBind)) -> Binding%(is-CBind):
  a = arg.arg
  v = arg.val
  CBind(a, desugar(v))
where:
  desugar-bind(ExtBind("x", numExt(5))) is CBind("x", numC(5))
end

## Especial function that desugars cond into an if statement
fun desugar-cond(cnds :: List<CaseStmt>) -> ExprC:
  cases (List) cnds:
    | empty => raise("Cond with no cases!")
    | link(f,r) =>
      cases (List) r:
        | empty => # we're at the last one
          cases (CaseStmt) f:
            | quesStmt(c,b) => raise("Unexpected 'case': else must be last in cond.")
            | elseStmt(b) => desugar(b)
          end
        | link(_,_) => # not the last one
          cases (CaseStmt) f:
            | elseStmt(b) => raise("Unexpected 'else': else must be last in cond.")
            | quesStmt(c,b) => ifC(desugar(c), desugar(b), desugar-cond(r))
          end
      end
  end
end

## ************** INTERPRETERS **************

## Interprets a Core Langauge Program to an actual value
fun interp-prog(prog :: Program%(is-progC), env :: Environment):
  interp(prog.src, prog.lib, env)
where:
  interp-prog(progC([list: fdC("foo", [list: "x"], lambdaC([list: idC("y")], plusC(idC("x"), idC("y"))))], lambAppC(appC("foo", [list: numC(42)]), [list: numC(3)])), mt-env) is 45
  interp-prog(progC(mt-libC, andC(trueC, trueC)), mt-env) is true
  interp-prog(progC([list: fdC("f", [list: ], trueC)], appC("f", empty)), mt-env) is true
  interp-prog(progC([list: fdC("f", [list: "x"], notC(idC("x")))], appC("f", [list: falseC])), mt-env) is true
  interp-prog(progC(empty, letStarC([list: CBind("x", numC(5)), CBind("y", numC(42))], plusC(idC("x"), idC("y")))), mt-env) is 47
  interp-prog(progC([list: fdC("foo", [list: "x"], lambdaC([list: idC("y")], lambdaC([list: idC("z")], plusC(idC("x"), plusC(idC("y"), idC("z"))))))], lambAppC(lambAppC(appC("foo", [list: numC(42)]), [list: numC(3)]), [list: numC(5)])), mt-env) is 50
end

## Interprets all Core expresions returning the final result
fun interp(expr :: ExprC, lib :: LibC, env :: Environment):
  cases (ExprC) expr:
      ##************Unary************
    | trueC => true
    | falseC => false
    | numC(n) => n
      ##************Binary***********
    | plusC(l, r) => interp(l, lib, env) + interp(r, lib, env)
    | multC(l, r) => interp(l, lib, env) * interp(r, lib, env)
    | divC(l, r) => interp(l, lib, env) / interp(r, lib, env)
    | modC(l, r) => num-modulo(interp(l, lib, env), interp(r, lib, env))
    | equalC(l, r) => interp(l, lib, env) == interp(r, lib, env)
    | biggerC(l, r) => interp(l, lib, env) > interp(r, lib, env)
    | smallerC(l, r) => interp(l, lib, env) < interp(r, lib, env)
    | notC(e) => not(interp(e, lib, env))
    | andC(l, r) => interp(l, lib, env) and interp(r, lib, env)
    | orC(l, r) => interp(l, lib, env) or interp(r, lib, env)
      ##***************Rest***********
    | ifC(c, t, f) =>
      if interp(c, lib, env):
        interp(t, lib, env)
      else:
        interp(f, lib, env)
      end
    | letC(e, v, body) => 
      new-env = link(bind(e, interp(v, lib, env)), env)## Adds the parameter to the enviroment before interpreting the body
      interp(body, lib, new-env)
    | letStarC(args, body) => 
      new-env = expandEnv-bindC(args, lib, env)## Adds all parameters to the enviroment before interpreting the body
      interp(body, lib, new-env)
    | lambdaC(args, b) => 
      interp(b, lib, env)
    | lambAppC(f, vals) =>
      new-env = expandEnv-lamb(vals, f, lib, env)## Adds all parameters to the enviroment before interpreting the body
      app = get-app(f)## There could be multiple lambAppC, but we need to interp the appC
      interp(app, lib, new-env)
    | appC(name, args) =>
      func = get-fun(name, lib) ## Gets the function from the library 
      new-env = expandEnv-aray(args, func.args, lib, env)## Adds all parameters to the enviroment before interpreting the body
      interp(func.body, lib, new-env)
    | idC(s) => get-param(s, env) ## Looks for the prameter's value and returns it
  end
where:
  interp(andC(notC(equalC(numC(3),numC(4))), ifC(biggerC(multC(numC(5), numC(3)), plusC(numC(5), numC(3))),trueC, falseC)), mt-libC, mt-env) is true
  f1 = fdC("a", empty, numC(10))
  f2 = fdC("b", [list: "x"], notC(idC("x")))
  f3 = fdC("c", [list: "x", "y"], equalC(idC("x"), idC("y")))
  lib = [list: f1, f2, f3]
  interp(appC("a", empty), lib, mt-env) is 10
  interp(appC("b", [list: falseC]), lib, mt-env) is true
  interp(appC("b", [list: trueC]), lib, mt-env) is false
  interp(plusC(appC("a",empty), numC(5)), lib, mt-env) is 15
  interp(divC(appC("a",empty), numC(2)), lib, mt-env) is 5
  interp(appC("c", [list: numC(4), numC(5)]), lib, mt-env) is false
  interp(appC("c", [list: numC(5), numC(5)]), lib, mt-env) is true
end

fun get-param(param :: String, env :: Environment): ## Looks for a parameter in the enviroment and reutrns its value
  cases (List) env:
    | empty => raise("get-param: Parameter not found: " + param)
    | link(f,r) =>
      if f.name == param: ## Compares the string with an element from the enviroment
        f.val
      else:
        get-param(param, r)
      end
  end
where:
  env = [list: bind("w", true), bind("x", false), bind("y",3), bind("z", 42)]
  get-param("w", env) is true
  get-param("x", env) is false
  get-param("y", env) is 3
  get-param("z", env) is 42
  get-param("n", env) raises "Parameter not found"
end

fun get-fun(func :: String, lib :: LibC) -> FunDefC: ## Looks for a function in the library and reutrns it
  cases (List) lib:
    | empty => raise("get-fun: Function not found: " + func)
    | link(f,r) =>
      if f.name == func:## Compares the string with an function from the library
        f
      else:
        get-fun(func, r)
      end
  end
where:
  f1 = fdC("a", empty, trueC)
  f2 = fdC("b", [list: "x"], notC(idC("x")))
  f3 = fdC("c", [list: "x", "y"], equalC(idC("x"), idC("y")))
  f4 = fdC("d", [list: "x", "y"], andC(idC("x"), idC("y")))
  lib = [list: f1, f2, f3, f4]
  get-fun("a", lib) is fdC("a", empty, trueC)
  get-fun("b", lib) is fdC("b", [list: "x"], notC(idC("x")))
  get-fun("c", lib) is fdC("c", [list: "x", "y"], equalC(idC("x"), idC("y")))
  get-fun("d", lib) is fdC("d", [list: "x", "y"], andC(idC("x"), idC("y")))
  get-fun("x", lib) raises "Function not found"
end

fun get-app(f :: ExprC) -> ExprC: ## Seek for the appC at the end of a lambAppCs chain
  cases(ExprC) f:
    | appC(name, arg) => f ## If f is a appC returns it
    | lambAppC(func, _) => get-app(f.func) ## If f is a lambAppC checks its body
    | else => raise("get-app: appC not found") ##Otherwise raise an error
  end
end

#######################Expand Enviroment##################

fun expandEnv-bindC(args :: List<Binding>, lib :: LibC, env :: Environment) -> Environment: ## This one takes a list of Bindings / designed to work with LetC
  cases (List) args:
    |empty => mt-env ## Returns empty if the list is empty
    |link(f, r) => ## Takes the first CBind
      name = f.name ## Takes the name
      value = f.val ## Takes the value
      link(bind(name, interp(value, lib, env)) , expandEnv-bindC(r, lib, env)) ## Adds it to the enviroment all recurs the rest of the list
    |else => raise("expandEnv: args do not contain a list")
  end
end

fun expandEnv-aray(actual :: List<ExprC>, formal :: List<String>, lib :: LibC, env :: Environment) -> Environment: ## This one takes two lists one for args, and anothe for vals / designed to work with appC
  block:
    when not(actual.length() == formal.length()):
      raise("expandEnv: Wrong number of arguments")
    end
    fun apply-interp(arg): interp(arg, lib, env) end## Helper function that aplays interp to one argument (perfect to use it along map)
    vals = actual.map(apply-interp) ## Interprets all values
    extensions = L.map2(bind, formal, vals) ## Creates an extension for env
    extensions.append(env) ## Adds the extension to the actual enviroment
  end
end

fun expandEnv-lamb(v :: List<ExprC>, app :: ExprC, lib :: LibC, env :: Environment) -> Environment:## This one takes a list of ExprC / designed to work with lambAppC
  fun apply-interp(arg): interp(arg, lib, env) end ## Helper function that applies interp to one argument (perfect to use it along map)
  fun idC-to-string(arg :: ExprC): ## Helper function that intepret idC (Because interp would return "arg"'s value, which has not been defined yet)
      cases(ExprC) arg:
        |idC(e) => e
        |else => raise("error")
      end
  end
  fun get-args(exp :: ExprC):## Helper function that takes the arguments from a lambdaC
    cases(ExprC) exp:
      |lambdaC(args, body) => 
        (args.map(idC-to-string)).append(get-args(body))
      |else => empty
    end
  end
  cases(ExprC) app: ## Checks which ExprC is app
    | appC(name, _) => ## This is the case that we are looking for
      func = get-fun(app.name, lib) ## Gets and processes the function, parameters, and values
      args = get-args(func.body)
      vals = v.map(apply-interp)
      if args.length() == vals.length(): ## Mekas sure we have the same amount of  parameters and values
        extensions = L.map2(bind, args, vals) ## Creates an extension for env
        extensions.append(env) ## Adds the extension to the actual enviroment
      else: raise("expandEnv-lamb: There are not equal amount of parameters and values" + torepr(vals))
      end
    | lambAppC(func, args) => expandEnv-lamb(v.append(args), app.func, lib, env) ## lambAppC means that it is necesary to keep loking
    | else => raise("expandEnv-lamb: Unexpected expresion: " + torepr(app)) ## Other case raises an erro
  end
  where:
  expandEnv-lamb([list: numC(3)], lambAppC(appC("foo", [list: numC(42)]), [list:numC(5)]), [list: fdC("foo", [list: "x"], lambdaC([list: idC("y")], lambdaC([list: idC("z")], plusC(idC("x"), plusC(idC("y"), idC("z"))))))] ,mt-env) is [list: bind("y", 3), bind("z", 5)]
end

### ****************** ALL-IN-ONE Functions ***********************

fun run(prog :: String):
  interp-prog(desugar-prog(parse-prog(S.read-s-exp(prog))),mt-env)
where:
  run("((def (foo x) (lambda (y) (+ x y))) ((foo 42) 3))") is 45
  run("((def (foo x) (lambda (y) (lambda (z) (+ x (+ y z))))) (((foo 42) 3) 5))") is 50
  run("((and true true))") is true
  run("((def (f) true) (f))") is true
  run("((def (f x) (not x)) (f false))") is true
  run("((def (a) true) (def (b x) (not x)) (def (c y) (if (b false) (a) y)) (c false))") is true
  run("((let* ((x 5) (y 42)) (+ x y)))") is 47
  run("((let (x 5) (+ x 2)))") is 7
end