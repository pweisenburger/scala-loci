package loci
package utility

import scala.annotation.{experimental, targetName}
import scala.quoted.*
import scala.util.control.NonFatal

object reflectionExtensions:
  extension (using Quotes)(symbol: quotes.reflect.Symbol)
    def isAbstract =
      (symbol.flags is quotes.reflect.Flags.Abstract) ||
      (symbol.flags is quotes.reflect.Flags.Deferred)

    def isMethod =
      symbol.isTerm &&
      !symbol.isClassConstructor &&
      (symbol.flags is quotes.reflect.Flags.Method)

    def isField =
      symbol.isTerm &&
      !(symbol.flags is quotes.reflect.Flags.Method) &&
      !(symbol.flags is quotes.reflect.Flags.Module) &&
      !(symbol.flags is quotes.reflect.Flags.Package)

    def isParam =
      symbol.flags is quotes.reflect.Flags.Param

    def isFieldAccessor =
      symbol.flags is quotes.reflect.Flags.FieldAccessor

    def isCaseAccessor =
      symbol.flags is quotes.reflect.Flags.CaseAccessor

    def isParamAccessor =
      symbol.flags is quotes.reflect.Flags.ParamAccessor

    def isStable =
      symbol.isTerm &&
      ((!(symbol.flags is quotes.reflect.Flags.Mutable) &&
        !(symbol.flags is quotes.reflect.Flags.Method)) ||
       (symbol.flags is quotes.reflect.Flags.StableRealizable))

    def isPublic =
      !(symbol.flags is quotes.reflect.Flags.Protected) &&
      !(symbol.flags is quotes.reflect.Flags.Private) &&
      !(symbol.flags is quotes.reflect.Flags.PrivateLocal) &&
      !(symbol.flags is quotes.reflect.Flags.Local)

    def isImplicit =
      (symbol.flags is quotes.reflect.Flags.Implicit) ||
      (symbol.flags is quotes.reflect.Flags.Given)

    def isExtensionMethod =
      symbol.flags is quotes.reflect.Flags.ExtensionMethod

    def isModuleDef =
      symbol.flags is quotes.reflect.Flags.Module

    def isPackageObject =
      (symbol.maybeOwner.flags is quotes.reflect.Flags.Package) &&
      (symbol.flags is quotes.reflect.Flags.Module) &&
      (symbol.name == "package" || (symbol.name endsWith "$package") ||
       symbol.name == "package$" || (symbol.name endsWith "$package$"))
  end extension

  extension (using Quotes)(flags: quotes.reflect.Flags)
    def &~(other: quotes.reflect.Flags) =
      import quotes.reflect.*
      import Flags.*

      var allFlags = List(
        Abstract, Artifact, Case, CaseAccessor, Contravariant, Covariant, Deferred,
        EmptyFlags, Enum, Erased, Exported, ExtensionMethod, FieldAccessor, Final,
        Given, HasDefault, Implicit, Infix, Inline, Invisible, Lazy, Local, Macro, Method, Module, Mutable,
        NoInits, Opaque, Open, Override, Package, Param, ParamAccessor, Private, PrivateLocal, Protected,
        Scala2x, Sealed, StableRealizable, Synthetic, Trait, Transparent)

      try
        val flagsClass = Class.forName("dotty.tools.dotc.core.Flags$")
        val flags = flagsClass.getField("MODULE$")
        val absOverride = flagsClass.getMethod("AbsOverride")
        absOverride.invoke(flags.get(null)) match
          case flags: Flags @unchecked if Flags.EmptyFlags.getClass.isInstance(flags) => allFlags ::= flags
          case _ =>
      catch
        case NonFatal(_) =>

      allFlags.foldLeft(EmptyFlags) { (result, flag) =>
        if (flags is flag) && !(other is flag) then result | flag else result
      }

    def cleaned =
      flags &~ quotes.reflect.Flags.EmptyFlags
  end extension

  extension (using Quotes)(tree: quotes.reflect.Tree)
    @targetName("safeShowTree") def safeShow: String = tree.safeShow("<?>", quotes.reflect.Printer.TreeCode)
    @targetName("safeShowTree") def safeShow(fallback: String): String = tree.safeShow(fallback, quotes.reflect.Printer.TreeCode)
    @targetName("safeShowTree") def safeShow(printer: quotes.reflect.Printer[quotes.reflect.Tree]): String = tree.safeShow("<?>", printer)
    @targetName("safeShowTree") def safeShow(fallback: String, printer: quotes.reflect.Printer[quotes.reflect.Tree]): String =
      try
        val result = tree.show(using printer).strip
        if result.nonEmpty then result else fallback
      catch
        case NonFatal(_) => fallback

    def posInUserCode =
      import quotes.reflect.*

      val splicePos = Position.ofMacroExpansion

      inline def isSynthetic(pos: Position) =
        pos.toString endsWith ">"

      inline def inUserCode(pos: Position) =
        pos.sourceFile == splicePos.sourceFile &&
        pos.start >= splicePos.start &&
        pos.end <= splicePos.end &&
        (pos.start != splicePos.start || (pos.end != splicePos.start && pos.end != splicePos.end))

      class PositionsAccumulator(filter: Position => Boolean) extends TreeAccumulator[List[Position]]:
        def foldTree(positions: List[Position], tree: Tree)(owner: Symbol) =
          if filter(tree.pos) then
            foldOverTree(tree.pos :: positions, tree)(owner)
          else
            foldOverTree(positions, tree)(owner)

      def accumulatePositions(filter: Position => Boolean) =
        val positions = PositionsAccumulator(filter).foldTree(List.empty, tree)(Symbol.noSymbol)
        Option.when(positions.nonEmpty) {
          positions reduce { (pos0, pos1) =>
            Position(splicePos.sourceFile, math.min(pos0.start, pos1.start), math.max(pos0.end, pos1.end))
          }
        }

      if inUserCode(tree.pos) && !isSynthetic(tree.pos) then
        tree.pos
      else
        accumulatePositions { pos => inUserCode(pos) && !isSynthetic(pos) } orElse
        accumulatePositions { inUserCode(_) } getOrElse
        Position.ofMacroExpansion
    end posInUserCode
  end extension

  extension (using Quotes)(term: quotes.reflect.Term)
    def substituteRefs(using Quotes)(
        from: quotes.reflect.Symbol,
        to: quotes.reflect.Symbol,
        owner: quotes.reflect.Symbol) =
      Substitutor.substituteRefsInTerm(Map(from -> to), owner, term)

    def substituteRefs(using Quotes)(
        substitutions: Map[quotes.reflect.Symbol, quotes.reflect.Symbol],
        owner: quotes.reflect.Symbol) =
      Substitutor.substituteRefsInTerm(substitutions, owner, term)
  end extension

  extension (using Quotes)(termModule: quotes.reflect.TermModule)
    def safeBetaReduce(term: quotes.reflect.Term) =
      import quotes.reflect.*

      object firstOwnerSymbolAccumulator extends TreeAccumulator[Option[Symbol]]:
        def foldTree(ownerSymbol: Option[Symbol], tree: Tree)(owner: Symbol) =
          ownerSymbol orElse {
            tree match
              case _: Definition => Some(tree.symbol.owner)
              case _ => foldOverTree(None, tree)(owner)
          }

      firstOwnerSymbolAccumulator.foldTree(None, term)(Symbol.noSymbol).fold(Term.betaReduce(term)) { owner =>
        val expr = Expr.betaReduce(term.asExpr)(using owner.asQuotes).asTerm
        Option.when(expr ne term) { expr }
      }
    end safeBetaReduce

    def safeTryBetaReduce(expr: quotes.reflect.Term) =
      quotes.reflect.Term.safeBetaReduce(expr) getOrElse expr
  end extension

  extension (using Quotes)(tpe: quotes.reflect.TypeRepr)
    @targetName("safeShowType") def safeShow: String = tpe.safeShow("<?>", quotes.reflect.Printer.SafeTypeReprCode)
    @targetName("safeShowType") def safeShow(fallback: String): String = tpe.safeShow(fallback, quotes.reflect.Printer.SafeTypeReprCode)
    @targetName("safeShowType") def safeShow(printer: quotes.reflect.Printer[quotes.reflect.TypeRepr]): String = tpe.safeShow("<?>", printer)
    @targetName("safeShowType") def safeShow(fallback: String, printer: quotes.reflect.Printer[quotes.reflect.TypeRepr]): String =
      try
        val result = tpe.show(using printer).strip
        if result.nonEmpty then result else fallback
      catch
        case NonFatal(_) => fallback

    def typeConstructor: quotes.reflect.TypeRepr =
      tpe match
        case quotes.reflect.AppliedType(tycon, _) => tycon
        case _ => tpe

    def typeArgs: List[quotes.reflect.TypeRepr] =
      tpe match
        case quotes.reflect.AppliedType(_, args) => args
        case _ => List.empty

    def typeArgVariances: List[quotes.reflect.Flags] =
      tpe match
        case TypeArgVariances(variances) => variances
        case _ => List.empty

    def resultType: quotes.reflect.TypeRepr =
      tpe match
        case tpe: quotes.reflect.MethodOrPoly => tpe.resType.resultType
        case tpe: quotes.reflect.ByNameType => tpe.underlying.resultType
        case _ => tpe

    def withResultType(res: quotes.reflect.TypeRepr): quotes.reflect.TypeRepr =
      import quotes.reflect.*
      tpe match
        case tpe @ MethodType(paramNames, paramTypes, resType) =>
          MethodType(paramNames)(_ => paramTypes, resType.withResultType(res).substituteParamRefs(tpe, _))
        case tpe @ PolyType(paramNames, paramBounds, resType) =>
          PolyType(paramNames)(_ => paramBounds, resType.withResultType(res).substituteParamRefs(tpe, _))
        case tpe @ TypeLambda(paramNames, paramBounds, resType) =>
          TypeLambda(paramNames, _ => paramBounds, resType.withResultType(res).substituteParamRefs(tpe, _))
        case ByNameType(underlying) =>
          ByNameType(underlying.withResultType(res))
        case _ =>
          res

    def contextFunctionResultType: quotes.reflect.TypeRepr =
      if tpe.isContextFunctionType then
        tpe.widenDealias.typeArgs.lastOption map { _.contextFunctionResultType } getOrElse tpe
      else
        tpe

    def finalResultType: quotes.reflect.TypeRepr =
      tpe.resultType.contextFunctionResultType

    def dealiasNonOpaque: quotes.reflect.TypeRepr =
      if tpe.typeSymbol.typeRef.isOpaqueAlias then tpe else tpe.dealias

    def widenDealias: quotes.reflect.TypeRepr =
      val dealiased = tpe.dealias
      if tpe != dealiased then
        dealiased.widenDealias
      else
        val widened = tpe.widen
        if tpe != widened then
          widened.widenDealias
        else
          tpe

    def widenDealiasNonOpaque: quotes.reflect.TypeRepr =
      val dealiased = tpe.dealiasNonOpaque
      if tpe != dealiased then
        dealiased.widenDealiasNonOpaque
      else
        val widened = tpe.widen
        if tpe != widened then
          widened.widenDealiasNonOpaque
        else
          tpe

    def stripLazyRef: quotes.reflect.TypeRepr =
      LazyRefStripping.strip(tpe)

    @experimental
    def substituteParamRefsByTermRefs(binder: quotes.reflect.Symbol) =
      import quotes.reflect.*

      def termSymbol(binder: TypeRepr, paramNum: Int, tpe: TypeRepr, paramSymss: List[List[Symbol]]): Option[Symbol] = tpe match
        case `binder` if paramSymss.nonEmpty && paramSymss.head.sizeIs > paramNum =>
          Some(paramSymss.head(paramNum))
        case tpe: LambdaType if paramSymss.nonEmpty =>
          termSymbol(binder, paramNum, tpe.resType, paramSymss.tail)
        case _ =>
          None

      object substitutor extends TypeMap(quotes):
        override def transform(tpe: TypeRepr) = tpe match
          case tpe: ParamRef =>
            termSymbol(tpe.binder, tpe.paramNum, binder.info, binder.paramSymss).fold(tpe) { _.termRef }
          case tpe =>
            super.transform(tpe)

      substitutor.transform(tpe)
    end substituteParamRefsByTermRefs

    def substitute(from: quotes.reflect.ParamRef, to: quotes.reflect.TypeRepr) =
      TypeParamSubstition.substitute(tpe, from, to)

    def substituteRefs(using Quotes)(from: quotes.reflect.Symbol, to: quotes.reflect.Symbol) =
      Substitutor.substituteRefsInType(Map(from -> to), tpe)

    def substituteRefs(using Quotes)(substitutions: Map[quotes.reflect.Symbol, quotes.reflect.Symbol]) =
      Substitutor.substituteRefsInType(substitutions, tpe)

    def substituteParamRefs(
        fromBinder: quotes.reflect.LambdaType | quotes.reflect.RecursiveType,
        toBinder: quotes.reflect.LambdaType | quotes.reflect.RecursiveType) =
      Substitutor.substituteParamRefsInType(Map(fromBinder -> toBinder), tpe)

    def substituteParamRefs(substitutionBinders: Map[
        quotes.reflect.LambdaType | quotes.reflect.RecursiveType,
        quotes.reflect.LambdaType | quotes.reflect.RecursiveType]) =
      Substitutor.substituteParamRefsInType(substitutionBinders, tpe)

    def resolvedMemberType(symbol: quotes.reflect.Symbol): Option[quotes.reflect.TypeRepr] =
      import quotes.reflect.*
      val baseType = tpe.baseType
      val memberTypeInRefinement =
        if symbol.isType then baseType.typeMemberTypeInRefinement(symbol.name)
        else if symbol.isField then baseType.fieldMemberTypeInRefinement(symbol.name)
        else None
      memberTypeInRefinement orElse {
        baseType.baseClasses collectFirst Function.unlift { base =>
          val overriding = symbol.overridingSymbol(base)
          Option.when(overriding.exists)(baseType.memberType(overriding))
        }
      }

    def resolvedTypeMemberType(name: String): Option[quotes.reflect.TypeRepr] =
      import quotes.reflect.*
      val baseType = tpe.baseType
      baseType.typeMemberTypeInRefinement(name) orElse {
        baseType.baseClasses collectFirst Function.unlift { base =>
          val symbol = base.typeMember(name)
          Option.when(symbol.exists)(baseType.memberType(symbol))
        }
      }

    def resolvedFieldMemberType(name: String): Option[quotes.reflect.TypeRepr] =
      import quotes.reflect.*
      val baseType = tpe.baseType
      baseType.fieldMemberTypeInRefinement(name) orElse {
        baseType.baseClasses collectFirst Function.unlift { base =>
          val symbol = base.fieldMember(name)
          Option.when(symbol.exists)(baseType.memberType(symbol))
        }
      }

    def selectMemberType(name: String): Option[quotes.reflect.TypeRepr] =
      tpe.baseType.selectMember(_.typeMemberTypeInRefinement(name), quotes.reflect.TypeSelect(_, name), _.typeMember(name))

    def selectMemberField(name: String): Option[quotes.reflect.TypeRepr] =
      tpe.baseType.selectMember(_.fieldMemberTypeInRefinement(name), quotes.reflect.Select.unique(_, name), _.fieldMember(name))

    private inline def baseType = tpe match
      case quotes.reflect.TypeBounds(_, hi) => hi
      case _ => tpe

    private inline def selectMember(
        inline memberInRefinement: quotes.reflect.TypeRepr => Option[quotes.reflect.TypeRepr],
        inline select: quotes.reflect.Term => quotes.reflect.Tree,
        inline lookup: quotes.reflect.Symbol => quotes.reflect.Symbol): Option[quotes.reflect.TypeRepr] =
      if memberInRefinement(tpe).isDefined then
        select(quotes.reflect.Select.unique(quotes.reflect.Literal(quotes.reflect.NullConstant()), "asInstanceOf").appliedToType(tpe)) match
          case tree: quotes.reflect.Term => Some(tree.tpe)
          case tree: quotes.reflect.TypeTree => Some(tree.tpe)
          case _ => None
      else
        tpe.baseClasses collectFirst Function.unlift { base =>
          val member = lookup(base)
          Option.when(member.exists)(tpe.select(member))
        }

    private inline def typeMemberTypeInRefinement(inline name: String) =
      tpe.memberTypeInRefinement(name) {
        case _: quotes.reflect.TypeBounds => true
        case _ => false
      }

    private inline def fieldMemberTypeInRefinement(inline name: String) =
      tpe.memberTypeInRefinement(name) {
        case _: quotes.reflect.TypeBounds | _: quotes.reflect.ByNameType | _: quotes.reflect.MethodOrPoly => false
        case _ => true
      }

    private def memberTypeInRefinement(member: String)(conforms: quotes.reflect.TypeRepr => Boolean): Option[quotes.reflect.TypeRepr] =
      import quotes.reflect.*
      tpe match
        case Refinement(parent, name, info) =>
          if name == member && conforms(info) then Some(info) else parent.memberTypeInRefinement(member)(conforms)
        case AndType(left, right) =>
          (left.memberTypeInRefinement(member)(conforms), right.memberTypeInRefinement(member)(conforms)) match
            case (Some(left), Some(right)) => Some(AndType(left, right))
            case (left, right) => left orElse right
        case _ =>
          val dealiased = tpe.dealiasNonOpaque
          if tpe != dealiased then
            dealiased.memberTypeInRefinement(member)(conforms)
          else
            val widened = tpe.widen
            if tpe != widened then
              widened.memberTypeInRefinement(member)(conforms)
            else
              None
  end extension

  extension (using Quotes)(thisTypeModule: quotes.reflect.ThisTypeModule)
    def apply(symbol: quotes.reflect.Symbol) = quotes.reflect.This(symbol).tpe

  private object Substitutor:
    def substituteRefsInTerm(using Quotes)(
        substitutions: Map[quotes.reflect.Symbol, quotes.reflect.Symbol],
        owner: quotes.reflect.Symbol,
        term: quotes.reflect.Term): quotes.reflect.Term =
      import quotes.reflect.*

      object substitutor extends SafeTreeMap(quotes):
        override def transformTerm(term: Term)(owner: Symbol) = term match
          case term: This =>
            substitutions.get(term.symbol).fold(super.transformTerm(term)(owner)) { This(_) }
          case term: Ident =>
            substitutions.get(term.symbol).fold(super.transformTerm(term)(owner)) { Ref(_) }
          case term: Select =>
            substitutions.get(term.symbol).fold(super.transformTerm(term)(owner)) { symbol =>
              transformTerm(term.qualifier)(owner).select(symbol)
            }
          case _ =>
            super.transformTerm(term)(owner)

        override def transformTypeTree(tree: TypeTree)(owner: Symbol) = tree match
          case Inferred() =>
            val tpe = substituteRefsInType(substitutions, tree.tpe)
            if tpe != tree.tpe then TypeTree.of(using tpe.asType) else tree
          case tree: TypeIdent =>
            substitutions.get(tree.symbol).fold(super.transformTypeTree(tree)(owner)) { TypeIdent(_) }
          case tree: TypeSelect =>
            substitutions.get(tree.symbol).fold(super.transformTypeTree(tree)(owner)) { symbol =>
              TypeSelect(transformTerm(tree.qualifier)(owner), symbol.name)
            }
          case _ =>
            super.transformTypeTree(tree)(owner)
      end substitutor

      substitutor.transformTerm(term)(owner)
    end substituteRefsInTerm

    def substituteRefsInType(using Quotes)(
        substitutions: Map[quotes.reflect.Symbol, quotes.reflect.Symbol],
        tpe: quotes.reflect.TypeRepr): quotes.reflect.TypeRepr =
      import quotes.reflect.*

      object substitutor extends TypeMap(quotes):
        override def transform(tpe: TypeRepr) = tpe match
          case tpe: NamedType =>
            substitutions.get(tpe.typeSymbol).fold(super.transform(tpe)) { transform(tpe.qualifier).select(_) }
          case tpe =>
            super.transform(tpe)

      substitutor.transform(tpe)
    end substituteRefsInType

    def substituteParamRefsInType(using Quotes)(
        substitutionBinders: Map[
          quotes.reflect.LambdaType | quotes.reflect.RecursiveType,
          quotes.reflect.LambdaType | quotes.reflect.RecursiveType],
        tpe: quotes.reflect.TypeRepr): quotes.reflect.TypeRepr =
      import quotes.reflect.*

      val substitutions = substitutionBinders.toMap[TypeRepr, LambdaType | RecursiveType]

      object substitutor extends TypeMap(quotes):
        override def transform(tpe: TypeRepr) = tpe match
          case ParamRef(binder, paramNum) =>
            substitutions.get(binder).fold(tpe) {
              case binder: MethodType => binder.param(paramNum)
              case binder: PolyType => binder.param(paramNum)
              case binder: TypeLambda => binder.param(paramNum)
              case _ => tpe
            }
          case RecursiveThis(binder) =>
            substitutions.get(binder).fold(tpe) {
              case binder: RecursiveType => binder.recThis
              case _ => tpe
            }
          case tpe =>
            super.transform(tpe)

      substitutor.transform(tpe)
    end substituteParamRefsInType
  end Substitutor

  trait TypeMap[Q <: Quotes & Singleton](val quotes: Q):
    import quotes.reflect.*

    private given quotes.type = quotes

    private inline def typeBounds(tpe: TypeRepr) = tpe match
      case tpe: TypeBounds => tpe
      case _ => TypeBounds(tpe, tpe)

    def transform(tpe: TypeRepr): TypeRepr = tpe match
      case tpe: NamedType =>
        def member(symbol: Symbol, name: String) = tpe match
          case _: TypeRef => symbol.typeMember(name)
          case _: TermRef => symbol.fieldMember(name)
        val qualifier = transform(tpe.qualifier)
        if qualifier != tpe.qualifier then
          val symbol = member(qualifier.typeSymbol, tpe.name)
          val memberSymbol = if symbol.exists then symbol else member(qualifier.termSymbol, tpe.name)
          qualifier.select(memberSymbol)
        else
          tpe
      case tpe: ThisType =>
        val tref = transform(tpe.tref)
        if tref != tpe.tref then ThisType(tref.typeSymbol) else tpe
      case SuperType(tpethis, tpesuper) =>
        val thistpe = transform(tpethis)
        val supertpe = transform(tpesuper)
        if thistpe != tpethis || supertpe != tpesuper then SuperType(thistpe, supertpe) else tpe
      case tpe: AppliedType =>
        val tycon = transform(tpe.tycon)
        val args = tpe.args map transform
        if tycon != tpe.tycon || args != tpe.args then AppliedType(tycon, args) else tpe
      case tpe: TypeBounds =>
        val low = transform(tpe.low)
        val hi = transform(tpe.hi)
        if low != tpe.low || hi != tpe.hi then TypeBounds(low, hi) else tpe
      case tpe: Refinement =>
        val parent = transform(tpe.parent)
        val info = transform(tpe.info)
        if parent != tpe.parent || info != tpe.info then Refinement(parent, tpe.name, info) else tpe
      case tpe: AndType =>
        val left = transform(tpe.left)
        val right = transform(tpe.right)
        if left != tpe.left || right != tpe.right then AndType(left, right) else tpe
      case tpe: OrType =>
        val left = transform(tpe.left)
        val right = transform(tpe.right)
        if left != tpe.left || right != tpe.right then OrType(left, right) else tpe
      case tpe: AnnotatedType =>
        val underlying = transform(tpe.underlying)
        if underlying != tpe.underlying then AnnotatedType(underlying, tpe.annotation) else tpe
      case tpe: MatchType =>
        val bound = transform(tpe.bound)
        val scrutinee = transform(tpe.scrutinee)
        val cases = tpe.cases map transform
        if bound != tpe.bound || scrutinee != tpe.scrutinee || cases != tpe.cases then MatchType(bound, scrutinee, cases) else tpe
      case tpe: MatchCase =>
        val pattern = transform(tpe.pattern)
        val rhs = transform(tpe.rhs)
        if pattern != tpe.pattern || rhs != tpe.rhs then MatchCase(pattern, rhs) else tpe
      case tpe: ByNameType =>
        val underlying = transform(tpe.underlying)
        if underlying != tpe.underlying then ByNameType(underlying) else tpe
      case tpe: MethodType =>
        val methodType = MethodType(tpe.paramNames)(
          binder => tpe.paramTypes map { param => transform(param).substituteParamRefs(tpe, binder) },
          transform(tpe.resType).substituteParamRefs(tpe, _))
        if methodType != tpe then methodType else tpe
      case tpe: PolyType =>
        val polyType = PolyType(tpe.paramNames)(
          binder => tpe.paramBounds map { param => typeBounds(transform(param).substituteParamRefs(tpe, binder)) },
          transform(tpe.resType).substituteParamRefs(tpe, _))
        if polyType != tpe then polyType else tpe
      case tpe: TypeLambda =>
        val typeLambda = TypeLambda(tpe.paramNames,
          binder => tpe.paramBounds map { param => typeBounds(transform(param).substituteParamRefs(tpe, binder)) },
          transform(tpe.resType).substituteParamRefs(tpe, _))
        if typeLambda != tpe then typeLambda else tpe
      case tpe: RecursiveType =>
        val recursiveType = RecursiveType(
          binder => transform(tpe.underlying).substituteParamRefs(tpe, binder))
        if recursiveType != tpe then recursiveType else tpe
      case _ =>
        tpe
  end TypeMap

  trait SafeTreeMap[Q <: Quotes & Singleton](val quotes: Q):
    import quotes.reflect.*

    private given quotes.type = quotes

    private object underlying extends TreeMap:
      override def transformTree(tree: Tree)(owner: Symbol): Tree =
        SafeTreeMap.this.transformTree(tree)(owner)
      override def transformStatement(tree: Statement)(owner: Symbol): Statement =
        SafeTreeMap.this.transformStatement(tree)(owner)
      override def transformTerm(tree: Term)(owner: Symbol): Term =
        SafeTreeMap.this.transformTerm(tree)(owner)
      override def transformTypeTree(tree: TypeTree)(owner: Symbol): TypeTree =
        SafeTreeMap.this.transformTypeTree(tree)(owner)
      override def transformCaseDef(tree: CaseDef)(owner: Symbol): CaseDef =
        SafeTreeMap.this.transformCaseDef(tree)(owner)
      override def transformTypeCaseDef(tree: TypeCaseDef)(owner: Symbol): TypeCaseDef =
        SafeTreeMap.this.transformTypeCaseDef(tree)(owner)
      override def transformStats(trees: List[Statement])(owner: Symbol): List[Statement] =
        SafeTreeMap.this.transformStats(trees)(owner)
      override def transformTrees(trees: List[Tree])(owner: Symbol): List[Tree] =
        SafeTreeMap.this.transformTrees(trees)(owner)
      override def transformTerms(trees: List[Term])(owner: Symbol): List[Term] =
        SafeTreeMap.this.transformTerms(trees)(owner)
      override def transformTypeTrees(trees: List[TypeTree])(owner: Symbol): List[TypeTree] =
        SafeTreeMap.this.transformTypeTrees(trees)(owner)
      override def transformCaseDefs(trees: List[CaseDef])(owner: Symbol): List[CaseDef] =
        SafeTreeMap.this.transformCaseDefs(trees)(owner)
      override def transformTypeCaseDefs(trees: List[TypeCaseDef])(owner: Symbol): List[TypeCaseDef] =
        SafeTreeMap.this.transformTypeCaseDefs(trees)(owner)
      override def transformSubTrees[Tr <: Tree](trees: List[Tr])(owner: Symbol): List[Tr] =
        SafeTreeMap.this.transformSubTrees(trees)(owner)

      def superTransformTree(tree: Tree)(owner: Symbol): Tree =
        super.transformTree(tree)(owner)
      def superTransformStatement(tree: Statement)(owner: Symbol): Statement =
        super.transformStatement(tree)(owner)
      def superTransformTerm(tree: Term)(owner: Symbol): Term =
        super.transformTerm(tree)(owner)
      def superTransformTypeTree(tree: TypeTree)(owner: Symbol): TypeTree =
        super.transformTypeTree(tree)(owner)
      def superTransformCaseDef(tree: CaseDef)(owner: Symbol): CaseDef =
        super.transformCaseDef(tree)(owner)
      def superTransformTypeCaseDef(tree: TypeCaseDef)(owner: Symbol): TypeCaseDef =
        super.transformTypeCaseDef(tree)(owner)
      def superTransformStats(trees: List[Statement])(owner: Symbol): List[Statement] =
        super.transformStats(trees)(owner)
      def superTransformTrees(trees: List[Tree])(owner: Symbol): List[Tree] =
        super.transformTrees(trees)(owner)
      def superTransformTerms(trees: List[Term])(owner: Symbol): List[Term] =
        super.transformTerms(trees)(owner)
      def superTransformTypeTrees(trees: List[TypeTree])(owner: Symbol): List[TypeTree] =
        super.transformTypeTrees(trees)(owner)
      def superTransformCaseDefs(trees: List[CaseDef])(owner: Symbol): List[CaseDef] =
        super.transformCaseDefs(trees)(owner)
      def superTransformTypeCaseDefs(trees: List[TypeCaseDef])(owner: Symbol): List[TypeCaseDef] =
        super.transformTypeCaseDefs(trees)(owner)
      def superTransformSubTrees[Tr <: Tree](trees: List[Tr])(owner: Symbol): List[Tr] =
        super.transformSubTrees(trees)(owner)
    end underlying

    def transformTree(tree: Tree)(owner: Symbol): Tree =
      underlying.superTransformTree(tree)(owner)
    def transformStatement(tree: Statement)(owner: Symbol): Statement =
      underlying.superTransformStatement(tree)(owner)
    def transformTerm(tree: Term)(owner: Symbol): Term =
      underlying.superTransformTerm(tree)(owner)
    def transformTypeTree(tree: TypeTree)(owner: Symbol): TypeTree = tree match
      case tree: TypeBoundsTree =>
        // workaround for issue: https://github.com/lampepfl/dotty/issues/17003
        TypeBoundsTree.copy(tree)(transformTypeTree(tree.low)(owner), transformTypeTree(tree.hi)(owner)).asInstanceOf[TypeTree]
      case _ =>
        underlying.superTransformTypeTree(tree)(owner)
    def transformCaseDef(tree: CaseDef)(owner: Symbol): CaseDef =
      underlying.superTransformCaseDef(tree)(owner)
    def transformTypeCaseDef(tree: TypeCaseDef)(owner: Symbol): TypeCaseDef =
      underlying.superTransformTypeCaseDef(tree)(owner)
    def transformStats(trees: List[Statement])(owner: Symbol): List[Statement] =
      underlying.superTransformStats(trees)(owner)
    def transformTrees(trees: List[Tree])(owner: Symbol): List[Tree] =
      underlying.superTransformTrees(trees)(owner)
    def transformTerms(trees: List[Term])(owner: Symbol): List[Term] =
      underlying.superTransformTerms(trees)(owner)
    def transformTypeTrees(trees: List[TypeTree])(owner: Symbol): List[TypeTree] =
      underlying.superTransformTypeTrees(trees)(owner)
    def transformCaseDefs(trees: List[CaseDef])(owner: Symbol): List[CaseDef] =
      underlying.superTransformCaseDefs(trees)(owner)
    def transformTypeCaseDefs(trees: List[TypeCaseDef])(owner: Symbol): List[TypeCaseDef] =
      underlying.superTransformTypeCaseDefs(trees)(owner)
    def transformSubTrees[Tr <: Tree](trees: List[Tr])(owner: Symbol): List[Tr] =
      underlying.superTransformSubTrees(trees)(owner)
  end SafeTreeMap

  trait TupleExtractor[Q <: Quotes & Singleton](val quotes: Q):
    import quotes.reflect.*

    private given quotes.type = quotes

    private val nil = TypeRepr.of[EmptyTuple].typeSymbol
    private val cons = TypeRepr.of[? *: ?].typeSymbol

    @targetName("unapplyType")
    def apply(elements: List[TypeRepr]): TypeRepr =
      if elements.nonEmpty && elements.sizeIs < 23 then
        defn.TupleClass(elements.size).typeRef.appliedTo(elements)
      else
        elements.foldRight[TypeRepr](nil.typeRef): (tpe, tuple) =>
          cons.typeRef.appliedTo(List(tpe, tuple))

    @targetName("unapplyTerm")
    def apply(elements: List[Term]): Term =
      if elements.nonEmpty && elements.sizeIs < 23 then
        Select.unique(Ref(defn.TupleClass(elements.size).companionModule), "apply")
          .appliedToTypes(elements map { _.tpe })
          .appliedToArgs(elements)
      else
        Select.unique(
          Select.unique(Ref(TypeRepr.of[scala.runtime.TupleXXL.type].termSymbol), "apply")
            .appliedTo(Typed(Repeated(elements, TypeTree.of[Any]), TypeTree.of[`<repeated>`[Any]])),
          "$asInstanceOf$").appliedToType(this(elements map { _.tpe }))

    @targetName("unapplyType")
    def unapply(tpe: TypeRepr): Option[List[TypeRepr]] = tpe match
      case _ if tpe.typeSymbol == nil =>
        Some(List.empty)
      case AppliedType(tycon, List(head, this(tail))) if tycon.typeSymbol == cons =>
        Some(head :: tail)
      case AppliedType(_, elements) if tpe.isTupleN =>
        Some(elements)
      case _ =>
        None

    @targetName("unapplyTerm")
    def unapply(term: Term): Option[List[Term]] = term match
      case Apply(TypeApply(fun @ Select(Apply(_, List(element1)), _), _), List(element2))
          if fun.symbol.owner == TypeRepr.of[ArrowAssoc].typeSymbol =>
        Some(List(element1, element2))
      case Apply(TypeApply(Select(qualifier, "apply"), _), elements)
          if defn.isTupleClass(qualifier.symbol.companionClass) =>
        Some(elements)
      case Apply(TypeApply(Select(New(tpt), "<init>"), _), elements)
          if defn.isTupleClass(tpt.tpe.typeSymbol) =>
        Some(elements)
      case Apply(Select(qualifier, "apply"), List(Typed(Repeated(elements, _), _)))
          if qualifier.symbol == TypeRepr.of[scala.runtime.TupleXXL.type].termSymbol =>
        Some(elements)
      case TypeApply(Select(
        Apply(Select(qualifier, "apply"), List(Typed(Repeated(elements, _), _))),
        "asInstanceOf" | "$asInstanceOf$"), _)
          if qualifier.symbol == TypeRepr.of[scala.runtime.TupleXXL.type].termSymbol =>
        Some(elements)
      case _ =>
        None
  end TupleExtractor

  extension (using Quotes)(printerModule: quotes.reflect.PrinterModule)
    def SafeTypeReprCode = safeTypeReprPrinter(quotes.reflect.Printer.TypeReprCode)
    def SafeTypeReprShortCode = safeTypeReprPrinter(quotes.reflect.Printer.TypeReprShortCode)
    def CompilerStyleTypeReprCode = CompilerStylePrinter.typeReprPrinter(quotes.reflect.Printer.SafeTypeReprCode)
    def CompilerStyleTypeReprShortFallbackCode = CompilerStylePrinter.typeReprPrinter(quotes.reflect.Printer.SafeTypeReprShortCode)
    def CompilerStyleTreeCode = CompilerStylePrinter.treePrinter(quotes.reflect.Printer.TreeCode)
    def CompilerStyleTreeShortFallbackCode = CompilerStylePrinter.treePrinter(quotes.reflect.Printer.TreeShortCode)

  private def safeTypeReprPrinter(using Quotes)(printer: quotes.reflect.Printer[quotes.reflect.TypeRepr]) =
    import quotes.reflect.*

    new Printer[TypeRepr]:
      def show(tpe: TypeRepr) = showType(tpe)

      private def showType(tpe: TypeRepr, typeArgument: Boolean = false): String =
        try tpe.show(using printer)
        catch case NonFatal(_) =>
          try tpe match
            case AppliedType(tycon, args) =>
              val tyconName = showType(tycon)
              val argsNames = args map { showType(_, typeArgument = true) }
              if tyconName.isEmpty then ""
              else if argsNames contains "" then tyconName
              else s"$tyconName[${argsNames.mkString(", ")}]"
            case tpe: NamedType if tpe.typeSymbol != defn.RootClass =>
              val owner = tpe.typeSymbol.owner
              val qualifierName = showType(tpe.qualifier)
              if qualifierName.nonEmpty then s"$qualifierName.${tpe.name}"
              else if owner != defn.RootClass then s"${owner.fullName}.${tpe.name}"
              else tpe.name
            case AnnotatedType(underlying, annotation) =>
              val underlyingName = showType(underlying)
              val annotationName =
                try annotation.show.stripPrefix("new ")
                catch case NonFatal(_) => ""
              if annotationName.nonEmpty then s"$underlyingName @$annotationName"
              else underlyingName
            case MatchType(_, scrutinee, cases) =>
              val casesNames = cases map { showType(_) }
              s"${showType(scrutinee)} match { ${casesNames.mkString(" ")} }"
            case MatchCase(pattern, rhs) =>
              s"case ${showType(pattern)} => ${showType(rhs)}"
            case ThisType(ref) if ref.typeSymbol.isPackageDef || ref.typeSymbol.isModuleDef =>
              showType(ref)
            case ThisType(ref) =>
              s"${showType(ref)}.this"
            case SuperType(ThisType(ref), _) =>
              s"${showType(ref)}.super"
            case SuperType(ref, _) =>
              s"${showType(ref)}.super"
            case Refinement(parent: Refinement, name, info) =>
              s"${showType(parent).stripSuffix(" }")}; ${showRefinement(name, info)} }"
            case Refinement(parent, name, info) =>
              s"${showType(parent)} { ${showRefinement(name, info)} }"
            case ByNameType(underlying) =>
              s"=> ${showType(underlying)}"
            case tpe @ MethodType(_, _, _: MethodOrPoly) =>
              showLambdaType(tpe, "(", ":", ")")
            case tpe: MethodType =>
              showLambdaType(tpe, "(", ":", "): ")
            case tpe @ PolyType(_, _, _: MethodOrPoly) =>
              showLambdaType(tpe, "[", "", "]")
            case tpe: PolyType =>
              showLambdaType(tpe, "[", "", "]: ")
            case tpe: TypeLambda =>
              showLambdaType(tpe, "[", "", "] =>> ")
            case ParamRef(binder: LambdaType, paramNum) =>
              binder.paramNames(paramNum)
            case tpe: AndType =>
              showAndOrType(tpe, "&")
            case tpe: OrType =>
              showAndOrType(tpe, "|")
            case TypeBounds(low, hi) =>
              if typeArgument then
                s"? >: ${showType(low)} <: ${showType(hi)}"
              else
                s">: ${showType(low)} <: ${showType(hi)}"
            case ConstantType(constant) =>
              constant.value.toString
            case _ =>
              ""
          catch case NonFatal(_) => ""

      private def showLambdaType(tpe: LambdaType, open: String, mid: String, close: String) =
        val args = tpe.paramNames zip tpe.paramTypes map { (name, tpe) => s"$name$mid ${showType(tpe)}" }
        s"${args.mkString(open, ", ", close)}${showType(tpe.resType)}"

      private def showAndOrType(tpe: AndOrType, operator: String) =
        val leftName = showType(tpe.left)
        val rightName = showType(tpe.right)
        if leftName.nonEmpty && rightName.nonEmpty then s"($leftName $operator $rightName)"
        else if leftName.nonEmpty then leftName
        else if rightName.nonEmpty then rightName
        else ""

      private def showRefinement(name: String, info: TypeRepr) = info match
        case _: TypeBounds =>
          s"type $name ${showType(info)}"
        case ByNameType(underlying) =>
          s"def $name: ${showType(underlying)}"
        case _: MethodOrPoly =>
          s"def $name${showType(info)}"
        case _ =>
          s"val $name: ${showType(info)}"
  end safeTypeReprPrinter

  private object CompilerStylePrinter:
    private val (printType, printTree) =
      try
        val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
        val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
        val typeClass = Class.forName("dotty.tools.dotc.core.Types$Type")
        val treeClass = Class.forName("dotty.tools.dotc.ast.Trees$Tree")
        val printerClass = Class.forName("dotty.tools.dotc.printing.Printer")
        val textClass = Class.forName("dotty.tools.dotc.printing.Texts$Text")

        val ctx = quotesImplClass.getMethod("ctx")
        val printer = contextClass.getMethod("printer")
        val typeToText = printerClass.getMethod("toText", typeClass)
        val treeToText = printerClass.getMethod("toText", treeClass)
        val mkString = textClass.getMethod("mkString", classOf[Int], classOf[Boolean])

        def print(quotes: Quotes, toText: java.lang.reflect.Method, value: Any) =
          try
            mkString.invoke(toText.invoke(printer.invoke(ctx.invoke(quotes)), value), Integer.MAX_VALUE, false) match
              case result: String => Some(result)
              case _ => None
          catch case NonFatal(_) => None

        (print(_, typeToText, _), print(_, treeToText, _))
      catch
        case NonFatal(_) =>
          ((quotes: Quotes, tpe: Any) => None, (quotes: Quotes, tree: Any) => None)

    def typeReprPrinter(using Quotes)(fallback: quotes.reflect.Printer[quotes.reflect.TypeRepr]) =
      new quotes.reflect.Printer[quotes.reflect.TypeRepr]:
        def show(tpe: quotes.reflect.TypeRepr) = printType(quotes, tpe) getOrElse fallback.show(tpe)

    def treePrinter(using Quotes)(fallback: quotes.reflect.Printer[quotes.reflect.Tree]) =
      new quotes.reflect.Printer[quotes.reflect.Tree]:
        def show(tree: quotes.reflect.Tree) = printTree(quotes, tree) getOrElse fallback.show(tree)
  end CompilerStylePrinter

  private object LazyRefStripping:
    private val stripLazyRef =
      try
        val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
        val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
        val typeClass = Class.forName("dotty.tools.dotc.core.Types$Type")

        val ctx = quotesImplClass.getMethod("ctx")
        val stripLazyRef = typeClass.getMethod("stripLazyRef", contextClass)

        { (quotes: Quotes, tpe: Any) =>
          import quotes.reflect.*

          try
            if typeClass.isInstance(tpe) then
              stripLazyRef.invoke(tpe, ctx.invoke(quotes)) match
                case tpe: TypeRepr @unchecked if typeClass.isInstance(tpe) =>
                  Some(tpe)
                case _ =>
                  None
            else
              None
          catch case NonFatal(_) => None
        }
      catch
        case NonFatal(_) =>
          (quotes: Quotes, tpe: Any) => None

    def strip(using Quotes)(tpe: quotes.reflect.TypeRepr) =
      stripLazyRef(quotes, tpe) getOrElse tpe
  end LazyRefStripping

  private object TypeParamSubstition:
    private val substituteTypeParam =
      try
        val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
        val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
        val typeClass = Class.forName("dotty.tools.dotc.core.Types$Type")
        val paramRefClass = Class.forName("dotty.tools.dotc.core.Types$ParamRef")

        val ctx = quotesImplClass.getMethod("ctx")
        val substParam = typeClass.getMethod("substParam", paramRefClass, typeClass, contextClass)

        { (quotes: Quotes, tpe: Any, from: Any, to: Any) =>
          import quotes.reflect.*

          try
            if paramRefClass.isInstance(from) && typeClass.isInstance(to) && typeClass.isInstance(tpe) then
              substParam.invoke(tpe, from, to, ctx.invoke(quotes)) match
                case tpe: TypeRepr @unchecked if typeClass.isInstance(tpe) =>
                  Some(tpe)
                case _ =>
                  None
            else
              None
          catch case NonFatal(_) => None
        }
      catch
        case NonFatal(_) =>
          (quotes: Quotes, tpe: Any, from: Any, to: Any) => None

    def substitute(using Quotes)(tpe: quotes.reflect.TypeRepr, from: quotes.reflect.ParamRef, to: quotes.reflect.TypeRepr) =
      substituteTypeParam(quotes, tpe, from, to) getOrElse tpe
  end TypeParamSubstition

  private object TypeArgVariances:
    private def varianceFlags(using Quotes)(flags: quotes.reflect.Flags) =
      import quotes.reflect.*
      if (flags is Flags.Covariant) && !(flags is Flags.Contravariant) then Flags.Covariant
      else if (flags is Flags.Contravariant) && !(flags is Flags.Covariant) then Flags.Contravariant
      else Flags.EmptyFlags

    private def variancesOfSymbol(using Quotes)(symbol: quotes.reflect.Symbol) =
      Some(symbol.declaredTypes collect { case symbol if symbol.isTypeParam => varianceFlags(symbol.flags) })

    private val variancesOfType =
      try
        val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
        val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
        val typeLambdaClass = Class.forName("dotty.tools.dotc.core.Types$TypeLambda")
        val lambdaParamClass = Class.forName("dotty.tools.dotc.core.Types$LambdaParam")

        val ctx = quotesImplClass.getMethod("ctx")
        val typeParams = typeLambdaClass.getMethod("typeParams")
        val paramVariance = lambdaParamClass.getMethod("paramVariance", contextClass)

        { (quotes: Quotes, tpe: Any) =>
          import quotes.reflect.*

          try
            if typeLambdaClass.isInstance(tpe) then
              typeParams.invoke(tpe) match
                case params: List[_] =>
                  val flagsClass = Flags.EmptyFlags.getClass
                  val context = ctx.invoke(quotes)
                  val variances = params map { param =>
                    paramVariance.invoke(param, context) match
                      case flags: Flags @unchecked if flagsClass.isInstance(flags) =>
                        Some(varianceFlags(using quotes)(flags))
                      case _ =>
                        None
                  }

                  if variances contains None then None
                  else Some(variances.flatten)

                case _ =>
                  None
            else
              None
          catch case NonFatal(_) => None
        }
      catch
        case NonFatal(_) =>
          (quotes: Quotes, tpe: Any) => None

    def unapply(using Quotes)(tpe: quotes.reflect.TypeRepr) =
      import quotes.reflect.*

      tpe match
        case tpe: LambdaType => variancesOfType(quotes, tpe)
        case TypeBounds(_, tpe: LambdaType) => variancesOfType(quotes, tpe)
        case ParamRef(PolyType(_, bounds, _), paramNum) =>
          bounds(paramNum).hi match
            case tpe: LambdaType => variancesOfType(quotes, tpe)
            case _ => variancesOfSymbol(tpe.typeSymbol)
        case _ => variancesOfSymbol(tpe.typeSymbol)
    end unapply
  end TypeArgVariances
end reflectionExtensions
