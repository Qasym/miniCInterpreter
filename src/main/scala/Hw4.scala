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

  case class Result(v: Val, m: Mem);
  case class UndefinedSemantics(msg: String = "", cause: Throwable = None.orNull) extends Exception("Undefined Semantics: " ++ msg, cause);
    
  
  def varToVal(params: List[Var], args: List[Var], paramEnv: Env, argsEnv: Env, itr: Int): Env = {
    if (params.size == itr) paramEnv;
    else {
      val new_env: Env = paramEnv + (params(itr) -> argsEnv(args(itr)));
      varToVal(params, args, new_env, argsEnv, itr + 1);
    }
  }

  def evalList(exprs: List[Expr], vals: List[Val], env: Env, mem: Mem, itr: Int): Tuple2[List[Val], Mem] = {
    if (exprs.size == itr) (vals, mem);
    else {
      val valorem = eval(env, mem, exprs(itr));
      evalList(exprs, valorem.v :: vals, env, valorem.m, itr + 1);
    }
  }

  def varToLoc(vars: List[Var], funcEnv: Env, top_mem: Int, itr: Int): Env = {
    if (vars.size == itr) funcEnv;
    else {
      val new_env: Env = funcEnv + (vars(itr) -> LocVal(top_mem));
      varToLoc(vars, new_env, top_mem + 1, itr + 1);
    }
  }

  def locToVal(top_mem: Int, vals: List[Val], mem: Mem, itr: Int): Mem = {
    if (vals.size == itr) mem;
    else {
      val new_mem: Mem = Mem(mem.m + (LocVal(top_mem) -> vals(itr)), top_mem + 1);
      locToVal(top_mem + 1, vals, new_mem, itr + 1);
    }
  }

  def accessField(rec: Val, field: Var): LocVal = rec match {
    case (rcrd: RecordVal) => if (rcrd.field == field) rcrd.loc;
                              else accessField(rcrd.next, field);
    case _ => throw new UndefinedSemantics(s"No such field as ${field}");
  }

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
      if (env.contains(Var(s))) 
        if (mem.m.contains(env(Var(s)))) Result(mem.m(env(Var(s))), mem);
        else throw new UndefinedSemantics(s"LocVal ${env(Var(s))} is not bound to a value");
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
        case (SkipVal, SkipVal) => Result(BoolVal(true), dextra.m);
        case _ => throw new UndefinedSemantics(s"No semantics for ${sinistra.v} == ${dextra.v}");
      }
    }
    case Iszero(c) => { //! provided pdf does not have semantics for this
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
      val primus = eval(env, mem, v);
      val new_env = env + (i -> LocVal(primus.m.top + 1));
      val new_mem = Mem(primus.m.m + (LocVal(primus.m.top + 1) -> primus.v), primus.m.top + 2);
      eval(new_env, new_mem, body);
    }
    case Proc(args, expr) => Result(ProcVal(args, expr, env), mem);
    case Asn(v, e) => {
      val resulten = eval(env, mem, e);
      Result(resulten.v, Mem(resulten.m.m + (env(v) -> resulten.v), resulten.m.top + 1));
    }
    case BeginEnd(expr) => {
      val resulten = eval(env, mem, expr);
      Result(resulten.v, resulten.m);
    }
    case FieldAccess(record, field) => {
      val rec = eval(env, mem, record);
      Result(rec.m.m(accessField(rec.v, field)), rec.m);
    }
    case FieldAssign(record, field, new_val) => {
      val rec = eval(env, mem, record);
      val valorem = eval(env, rec.m, new_val);
      val new_mem = Mem(valorem.m.m + (accessField(rec.v, field) -> valorem.v), valorem.m.top + 1);
      Result(valorem.v, new_mem);
    }
    case Block(f, s) => {
      val primus = eval(env, mem, f);
      val secundus = eval(env, primus.m, s);
      Result(secundus.v, secundus.m);
    }
    case PCallV(ftn, arg) => {
      val proc = eval(env, mem, ftn);
      val vals_mem = evalList(arg, Nil, env, mem, 0); //* This is a tuple of values and memory;
      proc.v match {
        case (procv: ProcVal) => {
          val new_env = varToLoc(procv.args, procv.env, vals_mem._2.top + 1, 0); //* This is an env with x1->l1
          val new_mem = locToVal(vals_mem._2.top + 1, vals_mem._1, vals_mem._2, 0); //* This is a mem with l1->v1
          eval(new_env, new_mem, procv.expr);
        }
        case _ => throw new UndefinedSemantics(s"${proc.v} is not a ProcVal!");
      }
    }
    case PCallR(ftn, arg) => {
      val proc = eval(env, mem, ftn);
      proc.v match {
        case (procv: ProcVal) => {
          if (arg.size != procv.args.size) throw new UndefinedSemantics("Not enough arguments for the procedure");
          eval(varToVal(procv.args, arg, procv.env, env, 0), proc.m, procv.expr);
        }
        case _ => throw new UndefinedSemantics(s"${proc.v} is not a ProcVal!");
      }
    }
    case WhileExpr(cond, body) => {
      val condition = eval(env, mem, cond);
      condition.v match {
        case BoolVal(b) => {
          if (b) {
            val resulten = eval(env, condition.m, body);
            eval(env, resulten.m, WhileExpr(cond, body));
          }
          else Result(SkipVal, condition.m);
        }
        case _ => throw new UndefinedSemantics(s"No semantics for while ${condition.v}");
      }
    }
    case RecordExpr(field, initVal, next) => {
      val resulten = eval(env, mem, initVal);
      val new_mem = resulten.m.extended(resulten.v);
      next match {
        case (rcrd: RecordExpr) => {
          val nextRec = eval(env, new_mem._1, rcrd);
          nextRec.v match {
            case (_nextRec: RecordValLike) => Result(RecordVal(field, LocVal(resulten.m.top), _nextRec), nextRec.m);
            case _ => throw new UndefinedSemantics(s"Undefined Semantics for ${nextRec}");
          }
        }
        case EmptyRecordExpr => Result(RecordVal(field, LocVal(resulten.m.top), EmptyRecordVal), new_mem._1);
      }
    }
    case EmptyRecordExpr => Result(EmptyRecordVal, mem);
  }

  def gc(env: Env, mem: Mem): Mem = {
    // TODO: Implement this method!
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