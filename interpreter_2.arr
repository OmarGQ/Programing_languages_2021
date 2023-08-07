### Omar I. Godinez

import s-exp as S
import lists as L

## ************** CORE DATA TYPES ********************

## A Library is a collection of Function Definitions 
## We can use "type" to alias another type.. list in this case
## it's also nice to alias constructors like empty to better
## match funciton names to an aliased type
type LibExt = List<FunDefExt>
mt-libExt = empty ## use empty in a cases expr., not mt-libExt

type LibC = List<FunDefC>
mt-libC = empty ## use empty in a cases expr., not mt-libC

## A "Program" Type
## Program is compirsed of a library of functions (lib)
## and source code (src)
data Program:
  | progExt(lib :: LibExt , src :: ExprExt)
  | progC(lib :: LibC, src :: ExprC)      
end

## Function Definition Types (Extended and Core)
data FunDefExt:
  | fdExt(name :: String, args :: List<String>, body :: ExprExt, values :: List<String>)
end
data FunDefC:
  | fdC(name :: String, args :: List<String>, body :: ExprC, values :: List<String>)
end

## Extended Language Expressions 
data ExprExt:
    ## TODO:  Complete this definition by replacing the no-arg stub
  | trueExt
  | falseExt
  | notExt(e :: ExprExt)
  | xorExt(argl :: ExprExt, argr :: ExprExt)
  | andExt(argl :: ExprExt, argr :: ExprExt)
  | orExt(argl :: ExprExt, argr :: ExprExt)
  | xnorExt(argl :: ExprExt, argr :: ExprExt)
  | nandExt(argl :: ExprExt, argr :: ExprExt)
  | norExt(argl :: ExprExt, argr :: ExprExt)
  | ifExt(c :: ExprExt, t :: ExprExt, e :: ExprExt)
  | idExt(s :: String)
end

## Core Language Expressions
data ExprC:
    ## TODO:  Complete this definition by replacing the no-arg stub
  | trueC
  | falseC
  | notC(e :: ExprC)
  | andC(argl :: ExprC, argr :: ExprC)
  | orC(argl :: ExprC, argr :: ExprC)
  | appC(name :: String, args :: ExprC)
  | ifC(c :: ExprC, t :: ExprC, e :: ExprC)
  | idC(s :: String)
end

## The value type returned by interp. 
type Value = Boolean

fun listing(args :: List<S.S-Exp>) -> List: 
  cases(List) args:
    | empty => empty 
    | link(f, r) => 
      cases(S.S-Exp) f:
        | s-sym(e) => link(e, listing(r)) 
        | s-num(e) => 
          if e == 1:
            link(true, listing(r))
          else if e == 0:
            link(false, listing(r))
          else:
            raise("No valid value introduced, only 1 for true and 0 for false")
          end
      end
          #link(f.s, defining_fun(r)) 
  end
end

## ************** PARSERS ********************

fun parse-prog(prog :: S.S-Exp) -> Program%(is-progExt):
  cases (S.S-Exp) prog:
    | s-list(shadow s) => 
      cases (List) s:
        | empty => empty
        | link(f, r) =>
          val = listing(L.get(r, 0).exps).rest
          def = parse-def(f, val)
          lib = link(def, mt-libExt)
          progExt(lib, def.body)
        |else => raise("parse: Not list")#Raises an error if it recieves an unexpected value
      end
    |else => raise("parse: Not list")#Raises an error if it recieves an unexpected value
  end
where:
  parse-prog(S.read-s-exp("((fun (f x) (not x)) (f 0))")) is progExt([list: fdExt("f", [list: "x"], notExt(idExt("x")), [list: false])], notExt(idExt("x")))
end

fun parse-def(adef :: S.S-Exp, val :: List<String>) -> FunDefExt:
  cases (S.S-Exp) adef:
    | s-list(shadow s) => 
      cases (List) s:
        | empty => raise("parse: unexpected empty list") 
        | link(op, args) =>
          ask:
            |op.s == "fun" then:
              definition = args.first.exps
              name = L.get(definition, 0).s
              fun_arg = listing(definition.rest)
              fdExt(name, fun_arg, parse-rest(args.rest.first), val)
            |otherwise: raise("parse: first operator must be fun")#Raises an error if the first operator is not fun
          end
        |else => raise("parse: Not list")#Raises an error if it recieves an unexpected value
      end
    |else => raise("parse: Not list")#Raises an error if it recieves an unexpected value
  end
where:
  parse-def(S.read-s-exp("(fun (f x) (not x))"), [list: false]) is fdExt("f", [list: "x"], notExt(idExt("x")), [list: false])
  parse-def(S.read-s-exp("(fun (f x y) (and x y))"), [list: false, true]) is fdExt("f", [list: "x", "y"], andExt(idExt("x"), idExt("y")), [list: false, true])
end

fun parse-rest(adef :: S.S-Exp) -> ExprExt:
  cases (S.S-Exp) adef:
    | s-sym(e) => idExt(e)
    | s-num(e) =>
      if e == 1:
        trueExt
      else if e == 0:
        falseExt
      else:
        raise("No valid value introduced, only 1 for true and 0 for false")
      end
    | s-list(shadow s) => 
      cases (List) s:
        | empty => raise("parse: unexpected empty list") 
        | link(op, args) =>
          len = args.length()   #Gets the number of arguments in the expression
          if len == 1:     
            arg = args.first#Gets the argument
            ask: #Identifies the operator and returns the expresion in ArthExt
              |op.s == "not" then: notExt(parse-rest(arg))
              |otherwise: raise("parse: Nonexistent operator")#Raises an error if the operator does not exist
            end
          else:
            if op.s == "if":
              con = args.first
              thn = args.rest.first
              els = L.get(args.rest.rest, 0)
              ifExt(parse-rest(con), parse-rest(thn), parse-rest(els))
            else:
              bi-def(op.s, args)
            end
          end
      end
    |else => raise("parse: Not value or list")#Raises an error if it recieves an unexpected value
  end
where:
  parse-rest(S.read-s-exp("(not x)")) is notExt(idExt("x"))
  parse-rest(S.read-s-exp("(and x y)")) is andExt(idExt("x"), idExt("y"))
  parse-rest(S.read-s-exp("(and x y z)")) is andExt(idExt("x"), andExt(idExt("y"), idExt("z")))
end

fun bi-def(op :: String, arg :: List<S.S-Exp>) ->ExprExt:
  len = arg.length()   #Gets the number of arguments in the expression
  if len > 2:
    argL = arg.first #Gets both elements
    argR = arg.rest
    ask:
      |op == "and" then: andExt(parse-rest(argL), bi-def(op, argR)) 
      |op == "or" then: orExt(parse-rest(argL), bi-def(op, argR))
      |op == "xor" then: xorExt(parse-rest(argL), bi-def(op, argR)) 
      |op == "nand" then: nandExt(parse-rest(argL), bi-def(op, argR)) 
      |op == "nor" then: norExt(parse-rest(argL), bi-def(op, argR)) 
      |op == "xnor" then: xnorExt(parse-rest(argL), bi-def(op, argR)) 
      |otherwise: raise("Nonexistent operator")
    end
  else:
    argL = arg.first #Gets both elements
    argR = L.get(arg, 1)
    ask:
      |op == "and" then: andExt(parse-rest(argL), parse-rest(argR)) 
      |op == "or" then: orExt(parse-rest(argL), parse-rest(argR))
      |op == "xor" then: xorExt(parse-rest(argL), parse-rest(argR)) 
      |op == "nand" then: nandExt(parse-rest(argL), parse-rest(argR)) 
      |op == "nor" then: norExt(parse-rest(argL), parse-rest(argR)) 
      |op == "xnor" then: xnorExt(parse-rest(argL), parse-rest(argR)) 
      |otherwise: raise("Nonexistent operator")
    end
  end
end
## ************** DESUGARERS ****************

## Desugar an Extended Langauge Program to the Core Language
fun desugar-prog(prog :: Program%(is-progExt)) -> Program%(is-progC):
  extdef = L.get(prog.lib, 0)
  cdef = desugar-def(extdef)
  lib = link(cdef, mt-libC)
  progC(lib, appC(extdef.name, cdef.body))
where:
  desugar-prog(progExt([list: fdExt("f", [list: "x"], notExt(idExt("x")), [list: false])], notExt(idExt("x")))) is progC([list: fdC("f", [list: "x"], notC(idC("x")), [list: false])], appC("f", notC(idC("x"))))
  desugar-prog(progExt([list: fdExt("f", [list: "x"], ifExt(notExt(idExt("x")), trueExt, falseExt), [list: false])], notExt(idExt("x")))) is progC([list: fdC("f", [list: "x"], ifC(notC(idC("x")), trueC, falseC), [list: false])], appC("f", ifC(notC(idC("x")), trueC, falseC)))
end

## Desugar a Function Definition
fun desugar-def(def :: FunDefExt) -> FunDefC:
  fdC(def.name, def.args, desugar(def.body), def.values)
where:
  desugar-def(fdExt("f", [list: "x"], notExt(idExt("x")), [list: false])) is fdC("f", [list: "x"], notC(idC("x")), [list: false])
end

fun desugar(expr :: ExprExt) -> ExprC:
  cases (ExprExt) expr: #Identifies the EXPRExt expression and returns its equivalent in eExprC
    | trueExt => trueC
    | falseExt => falseC
    | idExt(e) => idC(e)
    | notExt(e) => notC(desugar(e))
    | andExt(x, y) => andC(desugar(x), desugar(y))
    | orExt(x, y) => orC(desugar(x), desugar(y))
    | xorExt(x, y) => andC(orC(desugar(x), desugar(y)), notC(andC(desugar(x), desugar(y))))
    | nandExt(x, y) => notC(andC(desugar(x), desugar(y)))
    | norExt(x, y) => notC(orC(desugar(x), desugar(y)))
    | xnor(x, y) => notC(andC(orC(desugar(x), desugar(y)), notC(andC(desugar(x), desugar(y)))))
    | ifExt(c, t, e) => ifC(desugar(c), desugar(t), desugar(e))
    | else => raise("desugar: Unexpected ExprExt expresion") #Raises an error if the expresion does not exist
  end
end
## ************** INTERPRETERS **************

## Interpretation Environment Binding
data Binding:
    ## Eager is Names -> Values (Booleans here)
    ## Lazy would be Names -> Expressions
  | bind(name :: String, val :: Value)    
end

## List of Bindings is an Environment
##  This would be an AWESOME place for a map
type Environment = List<Binding>
mt-env = empty
xtnd-env = link

fun interp-prog(prog :: Program%(is-progC), env :: Environment) -> Value:
  cases (ExprC) prog.src:
    | trueC => true
    | falseC => false
    | idC(e) => num-to-val(e, env)
    |appC(n, s) =>
      def = get-def(prog.lib, n) 
      arg = def.args
      val = def.values
      new_env = expandEnv(arg, val)
      interp-prog(progC(prog.lib, s),new_env)
    | notC(e) => not(interp-prog(progC(prog.lib, e), env))
    | andC(x, y) => interp-prog(progC(prog.lib, x), env) and interp-prog(progC(prog.lib, y), env)
    | orC(x, y) => interp-prog(progC(prog.lib, x), env) or interp-prog(progC(prog.lib, y), env)
    | ifC(cnd, thn, els) =>
      ic = interp-prog(progC(prog.lib, cnd), env)
      if ic:
        interp-prog(progC(prog.lib, thn), env)
      else:
        interp-prog(progC(prog.lib, els), env)
      end
    |else => raise("interp-prog: Nonexistent operator")
  end
where:
  interp-prog(progC([list: fdC("f", [list: "x"], notC(idC("x")), [list: false])], appC("f", notC(idC("x")))), mt-env) is true
  interp-prog(progC([list: fdC("f", [list: "x", "y"], andC(idC("x"), idC("y")), [list: false, true])], appC("f", andC(idC("x"), idC("y")))), mt-env) is false
end

fun expandEnv(args :: List<String>, val :: List) -> Environment:
  cases (List) args:
    |empty => mt-env
    |link(f, r) =>
      name = f
      value = val.first
      link(bind(name, value) , expandEnv(r, val.rest))
    |else => raise("expandEnv: args do not contain a list")
  end
where:
  expandEnv([list: "x"], [list: true]) is [list: bind("x", true)]
  expandEnv([list: "x", "y"], [list: true, false]) is [list: bind("x", true), bind("y", false)]
end

fun num-to-val(arg :: String, env :: Environment) -> Value:
  cases (List) env:
    | empty => raise("unbound identifier")
    | link(f, r) =>
      if arg == f.name:
        f.val
      else:
        num-to-val(arg, r)
      end
    |else => raise("num-to-val: env do not contain a list")
  end
end

fun get-def(lib :: LibC, func :: String) -> FunDefC:
  cases (List) lib:
    | empty => raise("unbound function")
    | link(f, r) =>
      if func == f.name:
        f
      else:
        get-def(func, r)
      end
    |else => raise("get-def: lib do not contain a list")
  end
end

### ****************** ALL-IN-ONE Functions ***********************

## all in one for programs where 
## the definitions are bundled in a list
## with the expression to be executed
fun run(prog :: String) -> Value:
  interp-prog(desugar-prog(parse-prog(S.read-s-exp(prog))),mt-env)
where:
  run("((fun (f) 1) (f))") is true
  run("((fun (negation x) (not x)) (negation 0))") is true
  run("((fun (g x y) (and (not x) y)) (g 0 1))") is true
  run("((fun (n x) (if (not x) 1 0)) (n 1))") is false
  run("((fun (Carry a b) (if (and a b) 1 0)) (Carry 1 1))") is true
  run("((fun (Addition a b) (xor a b)) (Addition 1 1))") is false
  run("((fun (Addition_with_carry a b c d) (xor c (xor d (if (and a b) 1 0)))) (Addition 1 1 0 0))") is true
  #run("((fun (Addition_with_carry a b c d e f g h) (xor d (xor h (if (xor c (xor g (if (xor b (xor f (if (and a e) 1 0))) 1 0))) 1 0)))) (Addition 1 1 1 1 0 0 1 1))") is false
  
end
#fun is define a function first the name and variables, then the action and to finish it calls it with the values
