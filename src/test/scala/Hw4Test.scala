import hw4._
import hw4._
import scala.collection.immutable.HashMap
import scala.collection.JavaConverters._


class HweTest extends org.scalatest.funsuite.AnyFunSuite {
val fibo = """
proc (x)
    if x <= 0 then 0 else
      if x <= 2 then 1 else
        let temp = 1 in
        let p = 1 in
        let ret = 1 in
        let y = 3 in
        begin while y <= x
          begin
            temp := ret;
            ret := p + ret;
            p := temp;
            y := y + 1
          end end;
        ret
        """
type Env = HashMap[Var,LocVal]
val testGc = List(
  (HashMap[Var,LocVal](),
  Mem(HashMap(LocVal(3) -> IntVal(13), LocVal(5) -> IntVal(9), LocVal(1) -> IntVal(10), LocVal(4) -> IntVal(21), LocVal(2) -> IntVal(13)),6),
  Mem(HashMap[LocVal,Val](),6))

  ,(HashMap(Var("temp") -> LocVal(2), Var("x") -> LocVal(1), Var("y") -> LocVal(5), Var("ret") -> LocVal(4), Var("p") -> LocVal(3)),
Mem(HashMap(LocVal(3) -> IntVal(13), LocVal(5) -> IntVal(9), LocVal(1) -> IntVal(10), LocVal(4) -> IntVal(21), LocVal(0) -> ProcVal(List(Var("x")),Ite(LTEExpr(Var("x"),Const(0)),Const(0),Ite(LTEExpr(Var("x"),Const(2)),Const(1),Let(Var("temp"),Const(1),Let(Var("p"),Const(1),Let(Var("ret"),Const(1),Let(Var("y"),Const(3),Block(BeginEnd(WhileExpr(LTEExpr(Var("y"),Var("x")),BeginEnd(Block(Block(Block(Asn(Var("temp"),Var("ret")),Asn(Var("ret"),Add(Var("p"),Var("ret")))),Asn(Var("p"),Var("temp"))),Asn(Var("y"),Add(Var("y"),Const(1))))))),Var("ret")))))))),HashMap()), LocVal(2) -> IntVal(13)),6),
Mem(HashMap(LocVal(3) -> IntVal(13), LocVal(5) -> IntVal(9), LocVal(1) -> IntVal(10), LocVal(4) -> IntVal(21), LocVal(2) -> IntVal(13)),6))

  ,(HashMap[Var,LocVal](Var("temp") -> LocVal(2)),
  Mem(HashMap(LocVal(3) -> IntVal(13), LocVal(5) -> IntVal(9), LocVal(1) -> IntVal(10), LocVal(4) -> IntVal(21), LocVal(2) -> IntVal(13)),6),
  Mem(HashMap[LocVal,Val](LocVal(2) -> IntVal(13)),6))

  ,(HashMap[Var,LocVal](Var("temp") -> LocVal(2)),
  Mem(HashMap(LocVal(3) -> IntVal(13), LocVal(5) -> IntVal(9), LocVal(1) -> IntVal(10), LocVal(4) -> IntVal(21), LocVal(2) -> LocVal(3)),6),
  Mem(HashMap[LocVal,Val](LocVal(2) -> LocVal(3), LocVal(3) -> IntVal(13) ),6))

  ,(HashMap[Var,LocVal](Var("temp") -> LocVal(2), Var("temp2")->LocVal(30)),
    Mem(HashMap[LocVal,Val](LocVal(3) -> RecordVal(Var("x"), LocVal(5), EmptyRecordVal), LocVal(5) -> IntVal(9), LocVal(1) -> IntVal(10), LocVal(4) -> IntVal(21), LocVal(2) -> LocVal(3), LocVal(0) -> IntVal(11),
      LocVal(30) -> ProcVal(List(Var("x")),Asn(Var("x"),Const(5)),HashMap[Var,LocVal](Var("x") -> LocVal(6))), LocVal(6) -> LocVal(14), LocVal(4) -> IntVal(1), LocVal(15) -> IntVal(7), LocVal(14) -> RecordVal(Var("x"), LocVal(17), EmptyRecordVal),
      LocVal(17) -> IntVal(8), LocVal(24) -> IntVal(10), LocVal(25) -> IntVal(5), LocVal(20) -> IntVal(1), LocVal(8) -> IntVal(1),
      LocVal(7) -> IntVal(3)),6), Mem(HashMap(LocVal(3) -> RecordVal(Var("x"),LocVal(5),EmptyRecordVal), LocVal(5) -> IntVal(9), LocVal(6) -> LocVal(14), LocVal(14) -> RecordVal(Var("x"),LocVal(17),EmptyRecordVal), LocVal(17) -> IntVal(8),
      LocVal(2) -> LocVal(3), LocVal(30) -> ProcVal(List(Var("x")),Asn(Var("x"),Const(5)),HashMap(Var("x") -> LocVal(6)))),6))

  ,(HashMap(Var("f") -> LocVal(0), Var("y") -> LocVal(1)),Mem(HashMap(LocVal(3) -> IntVal(5), LocVal(1) -> IntVal(10), LocVal(0) -> ProcVal(List(Var("x"), Var("y")),Asn(Var("x"),Const(5)),HashMap()), LocVal(2) -> IntVal(10)),4),
    Mem(HashMap(LocVal(1) -> IntVal(10), LocVal(0) -> ProcVal(List(Var("x"), Var("y")),Asn(Var("x"),Const(5)),HashMap())),4))
  ,(HashMap(Var("z") -> LocVal(2), Var("f") -> LocVal(0), Var("y") -> LocVal(1)),Mem(HashMap(LocVal(3) -> IntVal(5), LocVal(1) -> IntVal(10), LocVal(4) -> IntVal(10), LocVal(0) -> ProcVal(List(Var("x"), Var("y")),Add(Sub(Var("x"),Var("y")),Const(10)),HashMap()), LocVal(2) -> IntVal(5)),5),
    Mem(HashMap(LocVal(1) -> IntVal(10), LocVal(0) -> ProcVal(List(Var("x"), Var("y")),Add(Sub(Var("x"),Var("y")),Const(10)),HashMap()), LocVal(2) -> IntVal(5)),5))
  ,(HashMap(Var("z") -> LocVal(2), Var("f") -> LocVal(0), Var("fibo") -> LocVal(5), Var("y") -> LocVal(1)),
    Mem(HashMap(LocVal(3) -> IntVal(5), LocVal(12) -> IntVal(11), LocVal(9) -> IntVal(34), LocVal(1) -> IntVal(10), LocVal(11) -> IntVal(55),
      LocVal(37) -> IntVal(13), LocVal(42) -> IntVal(34), LocVal(32) -> IntVal(1), LocVal(26) -> IntVal(5), LocVal(33) -> IntVal(8),
      LocVal(19) -> IntVal(4), LocVal(0) -> ProcVal(List(Var("x"), Var("y")),Add(Sub(Var("x"),Var("y")),Const(10)),HashMap()),
      LocVal(29) -> IntVal(5), LocVal(43) -> IntVal(10), LocVal(10) -> IntVal(34), LocVal(31) -> IntVal(7), LocVal(30) -> IntVal(8),
      LocVal(13) -> IntVal(1), LocVal(18) -> IntVal(2), LocVal(16) -> IntVal(1), LocVal(40) -> IntVal(1),
      LocVal(5) -> ProcVal(List(Var("x")),Ite(LTEExpr(Var("x"),Const(0)),Const(0),Ite(LTEExpr(Var("x"),Const(2)),Const(1),Let(Var("temp"),Const(1),Let(Var("p"),Const(1),Let(Var("ret"),Const(1),Let(Var("y"),Const(3),Block(BeginEnd(WhileExpr(LTEExpr(Var("y"),Var("x")),BeginEnd(Block(Block(Block(Asn(Var("temp"),Var("ret")),Asn(Var("ret"),Add(Var("p"),Var("ret")))),Asn(Var("p"),Var("temp"))),Asn(Var("y"),Add(Var("y"),Const(1))))))),Var("ret")))))))),HashMap(Var("z") -> LocVal(2), Var("f") -> LocVal(0), Var("y") -> LocVal(1))), LocVal(22) -> IntVal(3), LocVal(39) -> IntVal(9), LocVal(23) -> IntVal(5), LocVal(27) -> IntVal(6), LocVal(6) -> IntVal(10), LocVal(4) -> IntVal(10), LocVal(36) -> IntVal(1), LocVal(15) -> IntVal(3), LocVal(14) -> IntVal(1), LocVal(41) -> IntVal(21), LocVal(17) -> IntVal(1), LocVal(24) -> IntVal(1), LocVal(34) -> IntVal(13), LocVal(35) -> IntVal(8), LocVal(38) -> IntVal(21), LocVal(25) -> IntVal(3), LocVal(20) -> IntVal(1), LocVal(21) -> IntVal(2), LocVal(28) -> IntVal(1), LocVal(44) -> IntVal(1), LocVal(8) -> BoolVal(false), LocVal(7) -> BoolVal(false), LocVal(2) -> IntVal(5)),45),
    Mem(HashMap(LocVal(5) -> ProcVal(List(Var("x")),Ite(LTEExpr(Var("x"),Const(0)),Const(0),Ite(LTEExpr(Var("x"),Const(2)),Const(1),Let(Var("temp"),Const(1),Let(Var("p"),Const(1),Let(Var("ret"),Const(1),Let(Var("y"),Const(3),Block(BeginEnd(WhileExpr(LTEExpr(Var("y"),Var("x")),BeginEnd(Block(Block(Block(Asn(Var("temp"),Var("ret")),Asn(Var("ret"),Add(Var("p"),Var("ret")))),Asn(Var("p"),Var("temp"))),Asn(Var("y"),Add(Var("y"),Const(1))))))),Var("ret")))))))),HashMap(Var("z") -> LocVal(2), Var("f") -> LocVal(0), Var("y") -> LocVal(1))), LocVal(1) -> IntVal(10), LocVal(0) -> ProcVal(List(Var("x"), Var("y")),Add(Sub(Var("x"),Var("y")),Const(10)),HashMap()), LocVal(2) -> IntVal(5)),45))

  ,(HashMap[Var,LocVal](Var("temp") -> LocVal(2)),
  Mem(HashMap(LocVal(3) -> RecordVal(Var("x"), LocVal(5), EmptyRecordVal), LocVal(5) -> IntVal(9), LocVal(1) -> IntVal(10), LocVal(4) -> IntVal(21), LocVal(2) -> LocVal(3)),6),
  Mem(HashMap[LocVal,Val](LocVal(2) -> LocVal(3), LocVal(3) -> RecordVal(Var("x"), LocVal(5), EmptyRecordVal) , LocVal(5) -> IntVal(9)),6))
)

val miniCTestCases = List(
      ("skip",SkipVal)
      ,("true",BoolVal(true))
      ,("false",BoolVal(false))
      ,("let x = 1 in x",IntVal(1))
      ,("1",IntVal(1))
      ,("1 + 1", IntVal(2))
      ,("1 - 1", IntVal(0))
      ,("1 * 1", IntVal(1))
      ,("1 / 1", IntVal(1))
      ,("1 == 0",BoolVal(false))
      ,("1 == 1",BoolVal(true))
      ,("1 <= 0",BoolVal(false))
      ,("1 <= 10",BoolVal(true))
      ,("not true",BoolVal(false))
      ,("not false",BoolVal(true))
      ,("not 1 == 1",BoolVal(false))
      // ,("let Dung = {y:=100} in let r = {x:=Dung.y, K:={N:=3}} in r.x + r.K.N + 2",IntVal(105))
      ,("not 1 == 2",BoolVal(true))
      ,("if true then 1 else 2",IntVal(1))
      ,("if false then 1 else 2",IntVal(2))
      ,("let x = 0 in begin while x <= 10 x := x + 1 end ; x ", IntVal(11))
      ,("let x = 0 in begin while false x := x + 1 end ; x ", IntVal(0))
      ,("let x = 1 in x+1",IntVal(2))
      ,("proc (x) x + 10",ProcVal(List(Var("x")),Add(Var("x"),Const(10)),new Env()))
      ,("proc (x,y) x + y + 10",ProcVal(List(Var("x"), Var("y")),Add(Add(Var("x"),Var("y")),Const(10)),new Env()))
      ,("proc (x,z) x + x + 10",ProcVal(List(Var("x"), Var("z")),Add(Add(Var("x"),Var("x")),Const(10)),new Env()))
      ,("let f = proc (x,y)  x + y + 10 in f (1,2)",IntVal(13))
      ,("let f = proc (x)  x  + 10 in f (1)",IntVal(11))
      ,("let f = proc (x)  x  + 10 in let y = 10 in f <y>",IntVal(20))
      ,("let f = proc (x)  x := 5 in let y = 10 in begin f <y>; y end",IntVal(5))
      ,("let f = proc (x,y)  x - y + 10 in let y = 10 in let z = 5 in f <y,z>",IntVal(15))
      ,("let f = proc (x)  x := 5 in let y = 10 in begin f (y); y end",IntVal(10))
      ,("let x = 10 in x := 11",IntVal(11))
      ,("let x = 10 in x := skip",SkipVal)
      ,("{}",EmptyRecordVal)
      ,("{x := 1}",RecordVal(Var("x"),LocVal(0),EmptyRecordVal))
      ,("{y := 1, x := 1}",RecordVal(Var("y"),LocVal(0),RecordVal(Var("x"),LocVal(1),EmptyRecordVal)))
      ,("let z = 1 in begin {y := z := 0, x := z := 3}; z end",IntVal(3))
      ,("let r = {x:=1,y:=2} in r.x",IntVal(1))
      ,("let r = {x:=1,y:={z:=3}} in r.y.z",IntVal(3))
      ,("let r = {x:=1,y:={z:=3}} in r.y := 1",IntVal(1))
      ,("let r = {x:=1,y:={z:=3}} in begin r.y := 1; r.y end",IntVal(1))
      ,("begin {x:=1,y:={z:=3}} end . y := 1",IntVal(1))
      ,("let z = 1 in begin {x:=1,y:={k:=z := 2}} end . y := z",IntVal(2))
      ,("if 0 <= 1 then 1 else 2",IntVal(1))
      ,(s"let fibo = ${fibo} in fibo (0)",IntVal(0))
      ,(s"let fibo = ${fibo} in fibo (1)",IntVal(1))
      ,(s"let fibo = ${fibo} in fibo (2)",IntVal(1))
      ,(s"let fibo = ${fibo} in fibo (3)",IntVal(2))
      ,(s"let fibo = ${fibo} in fibo (4)",IntVal(3))
      ,(s"let fibo = ${fibo} in fibo (10)",IntVal(55))
    )
    val miniCErrorCases = List(
      "x"
      ,"1 + true"
      ,"1 (10)"
      ,"1 / 0"
      ,"not 1"
      ,"not skip"
      ,"if skip then 1 else 2"
      ,"if 1 then 1 else 2"
      ,"let x = 0 in begin while x x := x + 1 end ; x"
      ,"while x x := x + 1"
      ,"let f = proc (x)  x  + 10 in let y = 10 in f <z>"
      ,"y := 10"
    )
def compareRecordVal(r: RecordValLike, l: RecordValLike): Boolean = {
  (r,l) match {
    case (RecordVal(rf,rl,rn), RecordVal(lf, ll, ln)) => 
      rf == lf && rl.isInstanceOf[LocVal] && ll.isInstanceOf[LocVal] && compareRecordVal(rn, ln)
    case (EmptyRecordVal,EmptyRecordVal) => true
    case _ => false
  }
}
testGc.map((a: (Env, Mem , Mem)) => {
  val ref = a._3
  test(s"GcTest env: ${a._1}, mem: ${a._2}") {
    assert(MiniCInterpreter.gc(a._1, a._2) === a._3)
  }
})
  miniCTestCases.map((a: (String, Val)) => {
    val ref = a._2
    test(s"test with expected result: ${a._2} input: ${a._1}") {
      try {
        val res = MiniCInterpreter(a._1)._1
        (res,ref) match {
          case (l: RecordValLike, r: RecordValLike) => {
            if (compareRecordVal(l,r)) assert(true)
            else fail(s"${l} =/= ${r}")
          }
          case _ => assert(res === ref)
        }
      }
      catch {
        case e: StackOverflowError => fail("Stack overflow!")
      }
    }
  })

  miniCErrorCases.map((a: String) => {
    assertThrows[MiniCInterpreter.UndefinedSemantics] {
      try {
        MiniCInterpreter(a)
      }
      catch {
        case e: StackOverflowError => fail("Stack overflow!")
      }
    }
   })

}
