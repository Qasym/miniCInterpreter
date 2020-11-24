package hw4

import scala.collection.immutable.HashMap 
import hw4._


package object hw4 {
  type Env = HashMap[Var,LocVal]
}

case class Mem(m: HashMap[LocVal,Val], top: Int) {
  def extended(v: Val): (Mem, LocVal) = {
    val new_mem = Mem(m.updated(LocVal(top),v), top+1)
    (new_mem,LocVal(top))
  }
  def updated(l: LocVal, new_val: Val): Option[Mem] = {
    m.get(l) match {
      case Some(v) => Some(Mem(m.updated(l, new_val), top))
      case None => None
    }
  }
  def get(l: LocVal): Option[Val] = m.get(l)
  def getLocs(): List[LocVal] = m.keySet.toList
}

sealed trait Val
case object SkipVal extends Val
case class IntVal(n: Int) extends Val
case class BoolVal(b: Boolean) extends Val
case class ProcVal(args: List[Var], expr: Expr, env: Env) extends Val
case class LocVal(l: Int) extends Val
sealed trait RecordValLike extends Val
case object EmptyRecordVal extends RecordValLike
case class RecordVal(field: Var, loc: LocVal, next: RecordValLike) extends RecordValLike


sealed trait Program
sealed trait Expr extends Program
case object Skip extends Expr
case object False extends Expr
case object True extends Expr
case class NotExpr(expr: Expr) extends Expr
case class Const(n: Int) extends Expr
case class Var(s: String) extends Expr {
  override def toString = s"Var(${"\""}${s}${"\""})"
}
case class Add(l: Expr, r: Expr) extends Expr
case class Sub(l: Expr, r: Expr) extends Expr
case class Mul(l: Expr, r: Expr) extends Expr
case class Div(l: Expr, r: Expr) extends Expr
case class LTEExpr(l: Expr, r: Expr) extends Expr
case class EQExpr(l: Expr, r: Expr) extends Expr
case class Iszero(c: Expr) extends Expr
case class Ite(c: Expr, t: Expr, f: Expr) extends Expr
case class Let(i: Var, v: Expr, body: Expr) extends Expr
case class Proc(args: List[Var], expr: Expr) extends Expr
case class Asn(v: Var, e: Expr) extends Expr
case class BeginEnd(expr: Expr) extends Expr
case class FieldAccess(record: Expr, field: Var) extends Expr
case class FieldAssign(record: Expr, field: Var, new_val: Expr) extends Expr
case class Block(f: Expr, s: Expr) extends Expr
case class PCallV(ftn: Expr, arg: List[Expr]) extends Expr
case class PCallR(ftn: Expr, arg: List[Var]) extends Expr
case class WhileExpr(cond: Expr, body: Expr) extends Expr
sealed trait RecordLike extends Expr
case object EmptyRecordExpr extends RecordLike
case class RecordExpr(field: Var, initVal: Expr, next: RecordLike) extends RecordLike








object MiniCInterpreter {

  case class Result(v: Val, m: Mem)
  case class UndefinedSemantics(msg: String = "", cause: Throwable = None.orNull) extends Exception("Undefined Semantics: " ++ msg, cause)
    
  
  def eval(env: Env, mem: Mem, expr: Expr): Result = expr match {
    case Skip => {
      Result(SkipVal, mem);
    }
    case False => {
      Result(BoolVal(false), mem);
    }
    case True => {
      Result(BoolVal(true), mem);
    }
    case NotExpr(bool_expr) => {
      val result = eval(env, mem, bool_expr);
      result.v match {
        case BoolVal(b) => Result(BoolVal(!b), result.m);
        case _ => throw new UndefinedSemantics(s"No semantics for not ${result.v}");
      }
    }
    case Const(n) => {
      Result(IntVal(n), mem);
    }
    case Var(s) => {
      if (env.contains(s)) 
        if (mem.m.contains(env(s))) mem.m(env(s)) else throw new UndefinedSemantics(s"LocVal ${env(s)} is not bound to a value");
      else throw new UndefinedSemantics(s"The environment does not have ${s}");
    }
    case Add(l, r) => {
      val sinistra = eval(env, mem, l);
      val dextra = eval(env, sinistra.m, r);
      (sinistra.v, dextra.v) match {
        case (left_expr: IntVal, right_expr: IntVal) => Result(IntVal(left_expr.n + right_expr.n), dextra.m);
        case _ => throw new UndefinedSemantics(s"No semantics for ${sinistra.v} + ${dextra.v}");
      }
    }
    case Sub(l, r) => {
      val sinistra = eval(env, mem, l);
      val dextra = eval(env, sinistra.m, r);
      (sinistra.v, dextra.v) match {
        case (left_expr: IntVal, right_expr: IntVal) => Result(IntVal(left_expr.n - right_expr.n), dextra.m);
        case _ => throw new UndefinedSemantics(s"No semantics for ${sinistra.v} - ${dextra.v}");
      }
    }
    case Mul(l, r) => {
      val sinistra = eval(env, mem, l);
      val dextra = eval(env, sinistra.m, r);
      (sinistra.v, dextra.v) match {
        case (left_expr: IntVal, right_expr: IntVal) => Result(IntVal(left_expr.n * right_expr.n), dextra.m);
        case _ => throw new UndefinedSemantics(s"No semantics for ${sinistra.v} * ${dextra.v}");
      }
    }
    case Div(l, r) => {
      val sinistra = eval(env, mem, l);
      val dextra = eval(env, sinistra.m, r);
      (sinistra.v, dextra.v) match {
        case (left_expr: IntVal, right_expr: IntVal) => {
          if (right_expr.n == 0) throw new UndefinedSemantics("Division by zero");
          else Result(IntVal(left_expr.n / right_expr.n), dextra.m);
        }  
        case _ => throw new UndefinedSemantics(s"No semantics for ${sinistra.v} / ${dextra.v}");
      }
    }
    case LTEExpr(l, r) => {
      val sinistra = eval(env, mem, l);
      val dextra = eval(env, sinistra.m, r);
      (sinistra.v, dextra.v) match {
        case (left_expr: IntVal, right_expr: IntVal) => Result(BoolVal(left_expr.n <= right_expr.n), dextra.m);
        case _ => throw new UndefinedSemantics(s"No semantics for ${sinistra.v} <= ${dextra.v}");
      }
    }
    case EQExpr(l, r) => {
      val sinistra = eval(env, mem, l);
      val dextra = eval(env, sinistra.m, r);
      (sinistra.v, dextra.v) match {
        case (left_expr: IntVal, right_expr: IntVal) => Result(BoolVal(left_expr.n == right_expr.n), dextra.m);
        case (left_expr: BoolVal, right_expr: BoolVal) => Result(BoolVal(left_expr.b == right_expr.b), dextra.m);
        case (left_expr: SkipVal, right_expr: SkipVal) => Result(BoolVal(true), dextra.m);
        case _ => throw new UndefinedSemantics(s"No semantics for ${sinistra.v} == ${dextra.v}");
      }
    }
    case Iszero(c) => {
      val resulten = eval(env, mem, c);
      resulten.v match {
        case IntVal(n) => Result(BoolVal(n == 0), resulten.m);
        case _ => throw new UndefinedSemantics(s"No semantics for iszero(${resulten.v})")
      }
    }
    case Ite(c, t, f) => {
      val condition = eval(env, mem, c);
      condition.v match {
        case BoolVal(b) => {
          if (b) eval(env, condition.m, t);
          else eval(env, condition.m, f);
        }
        case _ => throw new UndefinedSemantics(s"No semantics for if ${condition.v}");
      }
    }
    case Let(i, v, body) => {

    }
    case Proc(args, expr) =>
      // ? How to treat the list of args ?
    }
    case Asn(v, e) => {

    }
    case BeginEnd(expr) => {

    }
    case FieldAccess(record, field) => {

    }
    case FieldAssign(record, field, new_val) => {

    }
    case Block(f, s) => {

    }
    case PCallV(ftn, arg) => {

    }
    case PCallR(ftn, arg) => {

    }
    case WhileExpr(cond, body) => {

    }
    case class RecordExpr(field, initVal, next) => {

    }
  }

  def gc(env: Env, mem: Mem): Mem = {
    Mem(mem.m, mem.top)
  }
  
  def apply(program: String): (Val, Mem) = {
    val parsed = MiniCParserDriver(program)
    val res = eval(new Env(), Mem(new HashMap[LocVal,Val],0), parsed)
    (res.v, res.m)
  }

}


object Hw4App extends App {
  
  println("Hello from Hw4!")

}