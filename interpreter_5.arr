use context essentials2021
#Omar I Godinez

import s-exp as S
import lists as L

## ************** CORE DATA TYPES ********************

##Binding onjects
data binding:
  | TBind(name :: String, val :: Type)                  ##Type binding
  | Bind(name :: String, val)                           ##Variable binding
  | BindFunc(name :: String, args :: List<TyExprC>, body)##Function binding
end

##Enviroments
type TyEnv = List<binding>##Type enviroment
mt-tnv = empty
xtnd-tnv = link

type Enviroment = List<binding>##Standar enviroment
mt-env = empty
xtnd-env = link

## Function Definitions
data TyExprC:
    # Value espressions
  | numC(n :: Number)
  | trueC
  | falseC
    # Binary Arithmetic expressions
  | plusC(l :: TyExprC, r :: TyExprC)
  | multC(l :: TyExprC, r :: TyExprC)
  | divC(l :: TyExprC, r :: TyExprC)
    # Numeric Comparison expressions
  | equalC(l :: TyExprC, r :: TyExprC)
  | greaterC(l :: TyExprC, r :: TyExprC)
    # Conditional expression
  | ifC(c :: TyExprC, t :: TyExprC, e :: TyExprC)
    # Function and let expresions
  | idC(s :: String)
  | letC(arg :: String, v :: TyExprC)
  | appC(f :: TyExprC, args :: List<TyExprC>)
  | fdC(name :: String, args :: List<TyExprC>, at :: Type, rt :: Type, body :: TyExprC)
  | localC(def :: List<TyExprC>, exp :: TyExprC)
end

##Type definitions
data Type:
  | numT
  | boolT
  | funT(a :: Type, r :: Type)
end

## ************** TYPE CHECKER ********************

##type checker main, identifies if we have just a single expression of a local expresion
fun tc-main(exp :: TyExprC, tnv :: TyEnv) -> Type:
  cases (TyExprC) exp:
    | localC(_,_) => tc-local(exp, tnv)
    | else => tc(exp, tnv)
  end
end

##Type check local expression
fun tc-local(local :: TyExprC%(is-localC), tnv :: TyEnv) -> Type:
  new-tnv = create-tnv(local.def, tnv) ##Creates an type enviroment with the initial definitions
  tc(local.exp, new-tnv) ##checks the instructions
end

##Checks and put all definitions into the type-enviroment
fun create-tnv(args :: List<TyExprC>, tnv :: TyEnv) -> TyEnv:
  cases (List) args:
    |empty => mt-tnv ## Returns empty if the list is empty
    |link(f, r) => ## Takes the first element of the list
      cases (TyExprC) f: ##It can be a function or a let expression
        | fdC(name, arg, at, rt, body) =>
          new-tnv = xtend-fun-env(arg, at, tnv) ##Creates an enviorement with the function's arguments
          bt = tc(body, new-tnv) ##CHecks the functions
          if bt == rt: ##Checks the return type is correct
            xtnd-tnv(TBind(name, funT(at, rt)), new-tnv) ##Returns the new type-enviroment
          else:
            raise("create-tnv: body type doesn't match declared type")
          end
        | letC(name, obj) =>
          xtnd-tnv(TBind(name, tc(obj, tnv)), create-tnv(r, tnv)) ##Returns the new type-enviroment
        | else => raise("create-tnv: expand-env: unexpected expresion")
      end 
  end
end

##The type cheker that make sure inputs and outputs types are correct
fun tc(e :: TyExprC, tnv :: TyEnv) -> Type:
  cases (TyExprC) e:
    | numC(_) => numT
    | trueC => boolT  
    | falseC => boolT
    | plusC(l, r) => tc-arith-binop(l, r, tnv)
    | multC(l, r) => tc-arith-binop(l, r, tnv)
    | divC(l, r) => tc-arith-binop(l, r, tnv)
    | equalC(l, r) => tc-logic-binop(l, r, tnv)
    | greaterC(l, r) => tc-logic-binop(l, r, tnv)
    | ifC(cnd, thn, els) =>
      cnd-t = tc(cnd, tnv) ##Checks the condition type
      if cnd-t == boolT:   ##And makes sure is a boolt type
        thn-t = tc(thn, tnv)
        els-t = tc(els, tnv) ##Checks then and else
        if thn-t == els-t:   ##These two must have the same type
          thn-t              ##And returns the return type
        else:
          raise("tc: Conditional branches don't match")
        end
      else:
        raise("tc: Conditional isn't Boolean")
      end
    | appC(f, args) =>
      f-t = tc(f, tnv) ##Gets function type
      a-t = check-args-type(args, f-t.a, tnv) ##Calls check-args-type
      if is-funT(f-t):
        if a-t == f-t.a: ##Makes sure the function and the arguments have the same type
          f-t.r  ##Returns the function's type
        else:
          raise("tc: Argument type doesn't match declared type")
        end
      else:
        raise("tc: Not a function in application position")
      end
    | idC(s) => ty-lookup(s, tnv, tnv)
    | else => raise("tc: Unexpected expression: " + e)
  end
end

##Type check arithmetic expressions, where both inputs must be numT type
fun tc-arith-binop(l :: TyExprC, r :: TyExprC, tnv :: TyEnv) -> Type:
  if (tc(l, tnv) == numT) and (tc(r, tnv) == numT):
    numT
  else:
    raise('tc-arith-binop: type error in arithmetic')
  end
end

##Type check logic expressions, where both inputs must be numT type
fun tc-logic-binop(l :: TyExprC, r :: TyExprC, tnv :: TyEnv) -> Type:
  if (tc(l, tnv) == numT) and (tc(r, tnv) == numT):
    boolT
  else:
    raise('tc-logic-binop: type error in arithmetic')
  end
end

##Finds an id from the type-enviroment and returns its type
fun ty-lookup(id :: String, tnv :: TyEnv, tnv2 :: TyEnv) -> Type:
  cases (List) tnv:
    | empty => raise("ty-lookup: Element not found: " + id)
    | link(f,r) =>
      if f.name == id: ## Compares the id with an element's name
        cases(binding) f:
          | TBind(_, val) => val
          | else => raise("ty-lookup: Unexpected element found in the enviroment: " + f)
        end
      else:
        ty-lookup(id, r, tnv2) ##Recurs until find the element
      end
  end
end

##Add multiple elemets with the same type to the type-enviroment
fun xtend-fun-env(args :: List<TyExprC>, ta :: Type, tnv :: TyEnv) -> TyEnv:
  cases(List) args:
    |empty => tnv
    |link(f, r) =>
      link(TBind(f.s, ta), xtend-fun-env(r, ta, tnv))
  end
end

##Checks that multiple elemets share the same type
fun check-args-type(args :: List<TyExprC>, ta :: Type, tnv :: TyEnv) -> Type:
  cases(List) args:
    | empty => ta ##Returns the type once it reached the end of the list
    | link(f, r) =>
      ty = tc(f, tnv) 
      if ty == ta: ##Compares the type
        check-args-type(r, ty, tnv) ##Recurs until reach the end of the list
      else:
        raise("The arguments do not share the same type")
      end
  end
end

## *************Type Check tests**********************************
##In these tests  it is expected to recive the expression type

check "TC Value espressions": 
  ## This tests the basic value expressions
  tc-main(numC(1), mt-tnv) is numT
  tc-main(trueC, mt-tnv) is boolT
end

check "TC Binary Arithmetic expressions":
  ## Here we test the expresions that recive two numT and return a numT
  lib = [list: TBind("x", numT), TBind("foo", funT(numT, numT))]
  tc-main(plusC(numC(1), numC(2)), mt-tnv) is numT
  tc-main(multC(numC(1), numC(2)), mt-tnv) is numT
  tc-main(divC(numC(1), numC(2)), mt-tnv) is numT
  ##It is also possible to look for elements storaged in the enviroment
  tc-main(multC(numC(1), idC("x")), lib) is numT
  tc-main(multC(numC(1), appC(idC("foo"), [list:numC(2)])), lib) is numT
  tc-main(plusC(multC(numC(1), numC(2)), divC(numC(1), numC(2))), mt-tnv) is numT
  tc-main(plusC(trueC, numC(2)), mt-tnv) raises "tc-arith-binop: type error in arithmetic"
  tc-main(multC(numC(1), idC("x")), mt-tnv) raises "ty-lookup: Element not found: x"
  tc-main(multC(numC(1), appC(idC("foo"), [list:numC(2)])), mt-tnv) raises "ty-lookup: Element not found: foo"
end

check "TC Numeric Comparison expressions":
  ## Here we test expressions that recive two numt and return a boolT
  tc-main(equalC(numC(1), numC(2)), mt-tnv) is boolT
  tc-main(greaterC(numC(1), numC(2)), mt-tnv) is boolT
  tc-main(greaterC(numC(1), divC(numC(1), numC(2))), mt-tnv) is boolT
  tc-main(equalC(numC(1), falseC), mt-tnv) raises "tc-logic-binop: type error in arithmetic"
end

check "TC Conditional expression":
  ## Here we test the conditional expression. This one evaluates a boolT expresion, and depending of the result, it returns one of two expressions that must share the same type
  lib = [list: TBind("x", numT), TBind("y", boolT)]
  tc-main(ifC(trueC, plusC(numC(1), numC(2)), numC(0)), mt-tnv) is numT
  tc-main(ifC(equalC(numC(1), numC(2)), trueC, falseC), mt-tnv) is boolT
  tc-main(ifC(idC("y"), trueC, falseC), lib) is boolT
  tc-main(ifC(equalC(numC(1), numC(2)), trueC, numC(5)), mt-tnv) raises "tc: Conditional branches don't match"
  tc-main(ifC(idC("x"), trueC, falseC), lib) raises "tc: Conditional isn't Boolean"
end

check "TC Functions and let expresions":
  ## Here we test mostly the type enviroment. using the expression localC we can add elements to the enviroment before executing an expresion. The things we can add to the enviroment are functions and variables.
  lib = [list: TBind("x", numT), TBind("y", numT), TBind("z", boolT), TBind("foo", funT(numT, boolT))]
  ## We can get an element from the enviroment by using idC
  tc-main(idC("x"), lib) is numT 
  tc-main(idC("x"), mt-tnv) raises "ty-lookup: Element not found: x"
  ## We can execute a function by using the expression appC, but it is also necesary to give values for each one of the function parameters. But we do not check the number of elements here.
  tc-main(appC(idC("foo"), [list: numC(5), numC(6)]), lib) is boolT
  tc-main(appC(idC("foo"), [list: numC(5), numC(6), numC(7)]), lib) is boolT
  tc-main(appC(idC("foo"), [list: numC(5)]), lib) is boolT
  tc-main(greaterC(idC("x"), idC("y")), lib) is boolT
  ## Here we use letC and fdC along with localC to add varuables and functions to the enviroment
  tc-main(localC([list: letC("x", numC(5)), letC("y", numC(10))], plusC(idC("x"), idC("y"))), mt-tnv) is numT
  tc-main(localC([list: fdC("foo", [list: idC("y"), idC("z")], numT, boolT, ifC(greaterC(idC("y"), idC("z")), trueC, falseC))], appC(idC("foo"), [list: numC(5), numC(6)])), mt-tnv) is boolT
  ## Here we have some cases of incorrect syntaxis
  tc-main(greaterC(idC("z"), idC("y")), lib) raises "tc-logic-binop: type error in arithmetic"
  tc-main(localC([list: letC("x", trueC), letC("y", numC(10))], plusC(idC("x"), idC("y"))), mt-tnv) raises "tc-arith-binop: type error in arithmetic"
  tc-main(localC([list: fdC("foo", [list: idC("y"), idC("z")], numT, numT, ifC(greaterC(idC("y"), idC("z")), trueC, falseC))], appC(idC("foo"), [list: numC(5), numC(6)])), mt-tnv) raises "create-tnv: body type doesn't match declared type"
end
## ******************** INTERPRETER ********************

##Interp-main identifies if we have a single expression of a local expression
fun interp-main(exp :: TyExprC, env :: Enviroment):
  cases (TyExprC) exp:
    | localC(_,_) => interp-local(exp, env)
    | else => interp(exp, env)
  end
end

##Interprets local expression
fun interp-local(local :: TyExprC%(is-localC), env :: Enviroment):
  new-env = create-env(local.def, env) ##Creates an enviroment with the initial definitions
  interp(local.exp, new-env) ##Interprets the instruction
end

##Interprests and puts all definitions into an enviroment
fun create-env(args :: List<TyExprC>, env :: Enviroment) -> Enviroment:
  cases (List) args:
    |empty => mt-env ## Returns empty if the list is empty
    |link(f, r) => ## Takes the first element of the list
      cases (TyExprC) f:
        | fdC(name, arg, _, _, body) => ##If it is a fdC it storages it as a function
          link(BindFunc(name, arg, body), create-env(r, env))
        | letC(name, obj) => ##If it is a letC it storages it as a variable
          link(Bind(name, interp(obj, env)), create-env(r, env))
        | else => raise("expand-env: unexpected expresion")
      end 
  end
end

##interprets the the expression
fun interp(exp :: TyExprC, env :: Enviroment):
  cases (TyExprC) exp:
    | numC(n) => n
    | trueC => true
    | falseC => false
    | plusC(l, r) => interp(l, env) + interp(r, env)
    | multC(l, r) => interp(l, env) * interp(r, env)
    | divC(l, r) => interp(l, env) / interp(r, env)
    | equalC(l, r) => interp(l, env) == interp(r, env)
    | greaterC(l, r) => interp(l, env) > interp(r, env)
    | ifC(c, t, e) =>
      c-val = interp(c, env)
      if c-val:
        interp(t, env)
      else:
        interp(e, env)
      end
    | idC(_) => lookup(exp.s, env)
    | appC(f, vals) =>
      fd = lookup(f.s, env)
      if length(vals) == length(fd.args):
        new-env = expand-env(fd.args, vals, env)
        interp(fd.body, new-env)
      else:
        raise("interp: appC - The number of arguments and values does not mach")
      end
  end
end

##Finds an id from the enviroment and returns its value
fun lookup(id :: String, env :: Enviroment):
  cases (List) env:
    | empty => raise("lookup: Element not found: " + id)
    | link(f,r) =>
      if f.name == id: ##Compares the id with an element's name
        cases(binding) f:
          | Bind(_, val) => val##For a variable
          | BindFunc(_, _, _) => f
        end
      else:
        lookup(id, r)
      end
  end
end

##Add multiple elemets to the enviroment
fun expand-env(args :: List<TyExprC>, vals :: List<TyExprC>, env :: Enviroment) -> Enviroment:
  cases (List) args:
    |empty => env ##When it reach the end of the list adds the old enviroment
    |link(f, r) => ##Takes the first element to add
      xtnd-env(Bind((args.get(0)).s, interp(vals.get(0), env)), expand-env(r, vals.drop(1), env))
  end
end

## *************Interpreter Check tests**********************************
##In these tests we test the execution of all core expressions and their outputs. We do not have much error tests here because tc should chach most of them

check "Interpreter Value espressions":
  ## This tests the basic value expressions. We expect to get a number or a boolean.
  interp-main(numC(1), mt-env) is 1
  interp-main(trueC, mt-env) is true
end

check "Interpreter Binary Arithmetic expressions":
  ## Here we test the arithmetic expresions that we expect to do and operation and return a numeric value
  lib = [list: Bind("x", 4), BindFunc("foo", [list: idC("x")], plusC(idC("x"), idC("x")))]
  interp-main(plusC(numC(1), numC(2)), mt-env) is 3
  interp-main(multC(numC(1), numC(2)), mt-env) is 2
  interp-main(divC(numC(1), numC(2)), mt-env) is 0.5
  interp-main(multC(numC(1), idC("x")), lib) is 4
  interp-main(multC(numC(1), appC(idC("foo"), [list:numC(2)])), lib) is 4
  interp-main(plusC(multC(numC(1), numC(2)), divC(numC(1), numC(2))), mt-env) is 2.5
  interp-main(multC(numC(1), idC("x")), mt-env) raises "lookup: Element not found: x"
end

check "Interpreter Numeric Comparison expressions":
  ## Here we test expressions that compare two numeric values and return a boolean value
  interp-main(equalC(numC(1), numC(2)), mt-env) is false
  interp-main(greaterC(numC(3), numC(2)), mt-env) is true
  interp-main(greaterC(numC(5), divC(numC(3), numC(9))), mt-env) is true
end

check "Interpreter Conditional expression":
  ## Here we test a if conditional expression. This one evaluates an expresion, and depending of the boolean result, it will execute its then or else expression.
  lib = [list: Bind("x", 4), Bind("y", true)]
  interp-main(ifC(trueC, plusC(numC(1), numC(2)), numC(0)), mt-env) is 3
  interp-main(ifC(equalC(numC(1), numC(2)), trueC, falseC), mt-env) is false
  interp-main(ifC(idC("y"), trueC, falseC), lib) is true
end

check "Interpreter Functions and let expresions":
  ## Here we test mostly the enviroment. Using the expression localC we add elements to the enviroment before executing an expresion. The things we can add to the enviroment are functions and variables.
  lib = [list: Bind("x", 4), Bind("y", 7), Bind("z", false), BindFunc("foo", [list: idC("a"), idC("b")], greaterC(idC("a"), idC("b")))]
  ## We can get an element from the enviroment by using idC
  interp-main(idC("x"), lib) is 4
  interp-main(idC("x"), mt-env) raises "lookup: Element not found: x"
  ## We can execute a function by using the expression appC, but it is also necesary to give values for each one of the function parameters.
  interp-main(appC(idC("foo"), [list: numC(5)]), lib) raises "interp: appC - The number of arguments and values does not mach"
  interp-main(appC(idC("foo"), [list: numC(5), numC(6)]), lib) is false
  interp-main(appC(idC("foo"), [list: numC(5), numC(6), numC(7)]), lib) raises "interp: appC - The number of arguments and values does not mach"
  interp-main(greaterC(idC("y"), idC("x")), lib) is true
  ## Here we use letC and fdC along with localC to add varuables and functions to the enviroment
  interp-main(localC([list: letC("x", numC(5)), letC("y", numC(10))], plusC(idC("x"), idC("y"))), mt-env) is 15
  interp-main(localC([list: fdC("foo", [list: idC("y"), idC("z")], numT, boolT, ifC(greaterC(idC("y"), idC("z")), trueC, falseC))], appC(idC("foo"), [list: numC(5), numC(6)])), mt-tnv) is false
end

## ******************** Main ********************

fun main(exp :: TyExprC):
  ty = tc-main(exp, mt-tnv) ##Executes the type checker to make sure everything is correct
  interp-main(exp, mt-env) ##Executes the interpreter to get the result
end

check "All together":
  ## For the final test we have a compilation of different test that shows how well the type checker and the interpreter works together
  main(localC([list: letC("x", numC(5)), letC("y", numC(10))], plusC(idC("x"), idC("y")))) is 15
  main(localC([list: fdC("foo", [list: idC("y"), idC("z")], numT, boolT, ifC(greaterC(idC("y"), idC("z")), trueC, falseC))], appC(idC("foo"), [list: numC(3), numC(6)]))) is false
  main(plusC(numC(5), numC(3))) is 8
  main(ifC(trueC, plusC(numC(1), numC(2)), numC(0))) is 3
  ## Chaching some errors
  main(localC([list: fdC("foo", [list: idC("y"), idC("z")], numT, boolT, ifC(greaterC(idC("y"), idC("z")), trueC, falseC))],appC(idC("foo"), [list: numC(5), numC(6), numC(7)]))) raises "interp: appC - The number of arguments and values does not mach"
  main(ifC(plusC(numC(5), numC(3)), trueC, falseC)) raises "tc: Conditional isn't Boolean"
end