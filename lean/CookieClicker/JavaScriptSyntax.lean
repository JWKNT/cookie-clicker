import Std

/-! Typed JavaScript syntax for the pinned source frontend.
This file defines syntax, not a native JavaScript correspondence theorem.
Strings retain UTF-16 code units, including unpaired surrogates. Number literals
retain their binary64 bit patterns. Unsupported syntax has an explicit marker;
an evaluator must reject that marker rather than treat it as an empty statement.
-/
namespace CookieClicker.JavaScript

abbrev JSString := List UInt16

def JSString.ofString (text : String) : JSString :=
  text.toList.flatMap fun c =>
    let n := c.toNat
    if n < 0x10000 then [UInt16.ofNat n]
    else let reduced := n - 0x10000
         [UInt16.ofNat (0xD800 + reduced / 0x400),
          UInt16.ofNat (0xDC00 + reduced % 0x400)]

inductive Literal where
  | null
  | boolean (value : Bool)
  | number (bits : UInt64)
  | string (value : JSString)
  deriving Repr, DecidableEq

inductive UnaryOp where
  | delete | void | typeOf | plus | minus | bitNot | not
  deriving Repr, DecidableEq

inductive UpdateOp where
  | increment | decrement
  deriving Repr, DecidableEq

inductive BinaryOp where
  | equal | notEqual | strictEqual | strictNotEqual
  | less | lessEqual | greater | greaterEqual
  | shiftLeft | shiftRight | unsignedShiftRight
  | add | subtract | multiply | divide | remainder
  | bitOr | bitXor | bitAnd | inOp | instanceOf
  deriving Repr, DecidableEq

inductive LogicalOp where
  | and | or
  deriving Repr, DecidableEq

inductive AssignmentOp where
  | assign | add | subtract | multiply | divide | remainder
  | shiftLeft | shiftRight | unsignedShiftRight | bitOr | bitXor | bitAnd
  deriving Repr, DecidableEq

inductive PropertyName where
  | identifier (name : String)
  | string (name : JSString)
  | number (bits : UInt64)
  deriving Repr, DecidableEq

inductive PropertyKind where
  | init | get | set
  deriving Repr, DecidableEq

mutual
  inductive Expr where
    | identifier (name : String)
    | this
    | literal (value : Literal)
    | regexp (pattern : JSString) (flags : String)
    | array (elements : List (Option Expr))
    | object (properties : List ObjectProperty)
    | function (name : Option String) (parameters : List String)
        (body : List Stmt) (strict : Bool) (sourceText : Option JSString)
    | sequence (expressions : List Expr)
    | unary (operator : UnaryOp) (argument : Expr)
    | update (operator : UpdateOp) (argument : Expr) (isPrefix : Bool)
    | binary (operator : BinaryOp) (left right : Expr)
    | logical (operator : LogicalOp) (left right : Expr)
    | assignment (operator : AssignmentOp) (left right : Expr)
    | conditional (test consequent alternate : Expr)
    | member (object property : Expr) (computed : Bool)
    | call (callee : Expr) (arguments : List Expr)
    | clockRead (integer : Bool) (callee argument : Expr)
    | clockZero
    | textIndexZero
    | construct (callee : Expr) (arguments : List Expr)
    | unsupported (tag : String)
    deriving Repr

  inductive Stmt where
    | empty
    | expression (expression : Expr)
    | block (body : List Stmt)
    | variable (declarations : List (String × Option Expr))
    | functionDeclaration (name : String) (parameters : List String)
        (body : List Stmt) (strict : Bool) (sourceText : Option JSString)
    | ifThenElse (test : Expr) (consequent : Stmt) (alternate : Option Stmt)
    | while (test : Expr) (body : Stmt)
    | doWhile (body : Stmt) (test : Expr)
    | forLoop (initial : Option ForInit) (test update : Option Expr) (body : Stmt)
    | forIn (binding : ForInBinding) (object : Expr) (body : Stmt)
    | return (value : Option Expr)
    | throw (value : Expr)
    | break (label : Option String)
    | continue (label : Option String)
    | labeled (label : String) (body : Stmt)
    | tryCatchFinally (body : Stmt) (handler : Option (String × Stmt))
        (finalizer : Option Stmt)
    | unsupported (tag : String)
    deriving Repr

  inductive ObjectProperty where
    | mk (key : PropertyName) (kind : PropertyKind) (value : Expr)
    deriving Repr

  inductive ForInit where
    | expression (value : Expr)
    | variables (declarations : List (String × Option Expr))
    deriving Repr

  inductive ForInBinding where
    | variable (name : String)
    | reference (expression : Expr)
    deriving Repr
end

structure Program where
  body : List Stmt
  strict : Bool
  deriving Repr

end CookieClicker.JavaScript
