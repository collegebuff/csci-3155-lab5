object Lab5 extends jsy.util.JsyApplication {
  import jsy.lab5.ast._
  import jsy.lab5._
  
  /*
   * CSCI 3155: Lab 5
   * Niklas Fejes
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  /*** Helper: mapFirst to DoWith ***/
  
  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](f: A => Option[DoWith[W,A]])(l: List[A]): DoWith[W,List[A]] = l match {
    case Nil => doreturn(Nil)
    case h :: t => f(h) match {
      case None => for (tp <- mapFirstWith(f)(t)) yield h :: tp
      case Some(withhp) => for (hp <- withhp) yield hp :: t
    }
  }

  /*** Casting ***/
  
  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
    case (TNull, TObj(_)) => true
    case (_, _) if (t1 == t2) => true
    case (TObj(f1), TObj(f2)) =>
        val (small,big) = if (f1.size < f2.size) (f1,f2) else (f2,f1)
        small.forall(big.toList.contains)
    case (TInterface(tvar, t1p), _) => castOk(typSubstitute(t1p, t1, tvar), t2)
    case (_, TInterface(tvar, t2p)) => castOk(t1, typSubstitute(t2p, t2, tvar))
    case _ => false
  }
  
  /*** Type Inference ***/
  
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  } 
    
  def mut(m: PMode): Mutability = m match {
    case PName => MConst
    case PVar | PRef => MVar
  }
  
  def typeInfer(env: Map[String,(Mutability,Typ)], e: Expr): Typ = {
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw new StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) =>
        val (_, t) = env(x)
        t
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        case TString => typ(e2) match {
          case TString => TString
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Eq|Ne, e1, e2) => typ(e1) match {
        case t1 if !hasFunctionTyp(t1) => typ(e2) match {
          case t2 if (t1 == t2) => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TBool
          case tgot => err(tgot, e2)
        }
        case TString => typ(e2) match {
          case TString => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(And|Or, e1, e2) => typ(e1) match {
        case TBool => typ(e2) match {
          case TBool => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Seq, e1, e2) => typ(e1); typ(e2)
      case If(e1, e2, e3) => typ(e1) match {
        case TBool =>
          val (t2, t3) = (typ(e2), typ(e3))
          if (t2 == t3) t2 else err(t3, e3)
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields map { case (f,t) => (f, typ(t)) })
      case GetField(e1, f) => typ(e1) match {
        case TObj(tfields) if (tfields.contains(f)) => tfields(f)
        case tgot => err(tgot, e1)
      } 
      
      case Function(p, paramse, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(rt)) =>
            val tprime = TFunction(paramse, rt)
            env + (f -> (MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with the parameters.
        val env2 = paramse match {
          case Left(params) =>
            params.foldLeft(env1)( (accEnv,key) => {
              val (s,t) = key
              accEnv + (s -> (MConst,t))
            }) 
          case Right((mode,x,t)) => mode match {
            case PName       => env1 + (x -> (MConst,t))
            case PVar | PRef => env1 + (x -> (MVar,t))
          }

        }
        // Infer the type of the function body
        val t1 = typeInfer(env2, e1)
        tann foreach { rt => if (rt != t1) err(t1, e1) };
        TFunction(paramse, t1)
      }
      
      case Call(e1, args) => (typ(e1),args) match {
        case (TFunction(Left(params), tret), args) if (params.length == args.length) => {
          (params, args).zipped.foreach {
            case ((_,pt),a) => if (pt != typ(a)) err(pt,e1)
          };
          tret
        }
        case (tgot @ TFunction(Right((mode,_,tp)), tret), e2 :: Nil) if (tp == typ(e2)) => mode match {
          case PRef => if (isLExpr(e2)) tret else err(tgot,e1)
          case PVar | PName => tret
        }
        case (tgot,_) => err(tgot, e1)
      }
      
      /*** Fill-in more cases here. ***/
      //case Decl(mut: Mutability, x: String, e1: Expr, e2: Expr) extends Expr
      case Decl(mut, x, e1, e2) => typeInfer(env + (x -> (mut,typ(e1))), e2)
      case Null => TNull
      case Unary(Cast(t),e) => if (castOk(typ(e),t)) t else err(t,e)
      case Assign(e1,e2) => e1 match {
        case Var(x) => env.get(x) match {
          case Some((mut,t)) if (mut == MVar && t == typ(e2)) => t
          case _ => err(typ(e1),e1)
        }
        case GetField(e,f) => typ(e) match {
          case TObj(fields) => fields.get(f) match {
            case Some(ft) if (ft == typ(e2)) => ft
            case _ => err(typ(e1),e1)
          }
          case _ => err(typ(e),e)
        }
        case _ => err(typ(e1),e1)
      }
        
        
        
        
      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }
  
  /*** Small-Step Interpreter ***/
  
  /* Do the operation for an inequality. */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2): @unchecked) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case (N(n1), N(n2)) =>
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }
  
  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = substitute(e, esub, x)
    val ep: Expr = avoidCapture(freeVars(esub), e)
    ep match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else e
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
      case Function(p, paramse, retty, e1) => (p,paramse) match {
        case (Some(p),_) if (p == x) => e
        case (_,Left(params)) if (!params.forall(_._1 != x)) => e
        case (_,Right((_,pname,_))) if (pname == x) => e
        case (_,_) => Function(p,paramse,retty,subst(e1))
      }
      case Call(e1, args) => Call(subst(e1), args map subst)
      case Obj(fields) => Obj(fields map { case (fi,ei) => (fi, subst(ei)) })
      case GetField(e1, f) => GetField(subst(e1), f)
      case Assign(e1, e2) => Assign(subst(e1), subst(e2))
      case InterfaceDecl(tvar, t, e1) => InterfaceDecl(tvar, t, subst(e1))
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))
    
    /*** Helpers for Call ***/
    
    def stepIfNotValue(e: Expr): Option[DoWith[Mem,Expr]] = if (isValue(e)) None else Some(step(e))

    def isObjectType(t: Typ): Boolean = t match {
      case TObj(_) | TInterface(_,TObj(_)) => true
      case _ => false
    }
    def isNullType(t: Typ): Boolean = t match {
      case TNull => true
      case _ => false
    }
 
    /* Check whether or not the argument expression is ready to be applied. */
    def argApplyable(mode: PMode, arg: Expr): Boolean = mode match {
      case PVar => isValue(arg)
      case PName => true
      case PRef => isLValue(arg)
    }

    /*** Body ***/
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => for (m <- doget) yield { println(pretty(m, v1)); Undefined }
      case Unary(Neg, N(n1)) => doreturn( N(- n1) )
      case Unary(Not, B(b1)) => doreturn( B(! b1) )
      case Binary(Seq, v1, e2) if isValue(v1) => doreturn( e2 )
      case Binary(Plus, S(s1), S(s2)) => doreturn( S(s1 + s2) )
      case Binary(Plus, N(n1), N(n2)) => doreturn( N(n1 + n2) )
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(inequalityVal(bop, v1, v2)) )
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 == v2) )
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 != v2) )
      case Binary(And, B(b1), e2) => doreturn( if (b1) e2 else B(false) )
      case Binary(Or, B(b1), e2) => doreturn( if (b1) B(true) else e2 )
      case Binary(Minus, N(n1), N(n2)) => doreturn( N(n1 - n2) )
      case Binary(Times, N(n1), N(n2)) => doreturn( N(n1 * n2) )
      case Binary(Div, N(n1), N(n2)) => doreturn( N(n1 / n2) )
      case If(B(b1), e2, e3) => doreturn( if (b1) e2 else e3 )
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) =>
        for (a <- Mem.alloc(e)) yield a
      // DoGetField
      case GetField(a @ A(_), f) => doget map { m =>
        m.get(a) match {
          case Some(Obj(fields)) if fields.contains(f) => fields(f)
          case _ =>  throw new StuckError(e)
        }
      }
        
      case Call(v1, args) if isValue(v1) =>
        def substfun(e1: Expr, p: Option[String]): Expr = p match {
          case None => e1
          case Some(x) => substitute(e1, v1, x)
        }
        (v1, args) match {
          /*** Fill-in the DoCall cases, the SearchCall2, the SearchCallVar, the SearchCallRef  ***/
          // DoCall / DoCallRec
          case (Function(p,Left(params),tann,e1),args) if (args forall isValue) =>
            if (params.length != args.length) throw StuckError(e);
            val e1p = (params,args).zipped.foldRight(e1) { case (((p,_),a),acc) => substitute(acc,a,p) }
            doreturn(substfun(e1p, p))

          // DoCallName / DoCallRecName
          case (Function(p,Right((PName,x1,typ)),tann,e1),e2 :: Nil) =>
            doreturn(substfun(substitute(e1,e2,x1),p))

          // DoCallVar / DoCallRecVar
          case (Function(p,Right((PVar,x1,typ)),tann,e1),v2 :: Nil) if isValue(v2) =>
            for (a <- Mem.alloc(v2)) yield substfun(substitute(e1,Unary(Deref,a),x1),p)

          // DoCallRef / DoCallRecRef
          case (Function(p,Right((PRef,x1,typ)),tann,e1),lv2 :: Nil) if isLValue(lv2) =>
            doreturn(substfun(substitute(e1,lv2,x1),p))

          // SearchCall2
          case (Function(_,Left(_),_,_),args) =>
            for (argsp <- mapFirstWith(stepIfNotValue)(args)) yield Call(v1,argsp)

          // SearchCallVar
          case (Function(_,Right((PVar,_,_)),_,_),e2 :: Nil) =>
            for (e2p <- step(e2)) yield Call(v1,List(e2p))
 
          // SearchCallRef
          case (Function(_,Right((PRef,_,_)),_,_),e2 :: Nil) if (!isLValue(e2)) =>
            for (e2p <- step(e2)) yield Call(v1,List(e2p))
 
          case _ => throw StuckError(e)
        } 
      
      // DoConst
      case Decl(MConst, x, v1, e2) if isValue(v1) => doreturn(substitute(e2, v1, x))
      // DoVar
      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        for (a <- Mem.alloc(v1)) yield substitute(e2,Unary(Deref,a),x)

      // DoAssignVar
      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        for (_ <- domodify { (m: Mem) => 
            if (!m.contains(a)) throw new StuckError(e)
            m + (a,v)
        }) yield v
    
      // DoAssignField
      case Assign(GetField(a @ A(_),f), vp) if isValue(vp) =>
        for (_ <- domodify { (m: Mem) => m.get(a) match {
            case Some(Obj(fields)) if fields.contains(f) =>
              m + (a,Obj(fields + (f -> vp)))
            case _ => throw new StuckError(e)
          }
        }) yield vp
    
      // DoDeref
      case Unary(Deref, a @ A(_)) => doget map { m =>
        m.get(a) match {
          case Some(e1) => e1
          case _ =>  throw new StuckError(e)
        }
      }
        
      /*** Fill-in more Do cases here. ***/
      
      
      /* Base Cases: Error Rules */
      /*** Fill-in cases here. ***/
      case Unary(Cast(t),e1) => e1 match {
        // DoCastNull
        case Null if isObjectType(t) => doreturn(Null)
        // DoCastObj / TypeErrorCastObj
        case a @ A(_) if isObjectType(t) => doget map { m =>
          val tfields : Map[String,Typ] = (t: @unchecked) match {
            case TObj(tfields) => tfields
            case TInterface(_,TObj(tfields)) => tfields
          }
          m.get(a) match {
            case Some(Obj(fields)) => 
              if (tfields.forall((t) => fields.contains(t._1))) a
              else throw new DynamicTypeError(e)
            case _ => throw new StuckError(e)
          }
        }
          
        // DoCast
        case v if isValue(v) => v match {
          case Null | A(_) => throw new StuckError(e)
          case _ => doreturn(v)
        }
        case _ => throw new StuckError(e)
      }

      // NullErrorGetField / NullErrorAssignField
      case GetField(Null,_) | Assign(GetField(Null,_),_) => throw new NullDereferenceError(e)


      /* Inductive Cases: Search Rules */
      case Print(e1) =>
        for (e1p <- step(e1)) yield Print(e1p)
      case Unary(uop, e1) =>
        for (e1p <- step(e1)) yield Unary(uop, e1p)
      case Binary(bop, v1, e2) if isValue(v1) =>
        for (e2p <- step(e2)) yield Binary(bop, v1, e2p)
      case Binary(bop, e1, e2) =>
        for (e1p <- step(e1)) yield Binary(bop, e1p, e2)
      case If(e1, e2, e3) =>
        for (e1p <- step(e1)) yield If(e1p, e2, e3)
      case Obj(fields) => fields find { case (_, ei) => !isValue(ei) } match {
        case Some((fi,ei)) =>
          for (eip <- step(ei)) yield Obj(fields + (fi -> eip))
        case None => throw StuckError(e)
      }
      // SearchGetField
      case GetField(e1, f) =>
        for (e1p <- step(e1)) yield GetField(e1p, f)
      
      /*** Fill-in more Search cases here. ***/
      case Decl(mod, x, e1, e2) =>
        for (e1p <- step(e1)) yield Decl(mod, x, e1p, e2)
      // SearchCall1
      case Call(e1,args) =>
        for (e1p <- step(e1)) yield Call(e1p, args)
      // SearchAssign1
      case Assign(e1,e2) if !isLValue(e1) =>
        for (e1p <- step(e1)) yield Assign(e1p,e2)
      // SearchAssign2
      case Assign(lv1,e2) =>
        for (e2p <- step(e2)) yield Assign(lv1,e2p)
        

      /* Everything else is a stuck error. */
      case _ => 
        println("error on: " + e)
        throw StuckError(e)
    }
  }

  /*** External Interfaces ***/

//  this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(500) // comment this out or set to None to not bound the number of steps.
  
  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  
  case class TerminationError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }
  
  def iterateStep(e: Expr): Expr = {
    require(closed(e), "not a closed expression: free variables: %s".format(freeVars(e)) )
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e)
      else if (isValue(e)) doreturn( e )
      else {
        for {
          m <- doget[Mem]
          _ = if (debug) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
          ep <- step(e)
          epp <- loop(ep, n + 1)
        } yield
        epp
      }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val (m,v) = loop(e, 0)(Mem.empty)
    if (debug) {
      println("Result:%n  %s%n  %s".format(m,v))
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(removeInterfaceDecl(jsy.lab5.Parser.parse(s)))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab5.Parser.parseFile(file)
      }} getOrElse {
        return
      }
      
    val exprlowered =
      handle(None: Option[Expr]) {Some{
        removeInterfaceDecl(expr)
      }} getOrElse {
        return
      }  
    
    handle() {
      val t = inferType(exprlowered)
    }
    
    handle() {
      val v1 = iterateStep(exprlowered)
      println(pretty(v1))
    }
  }
    
}
