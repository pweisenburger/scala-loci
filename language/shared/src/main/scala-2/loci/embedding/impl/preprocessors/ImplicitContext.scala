package loci
package embedding
package impl
package preprocessors

import scala.reflect.macros.blackbox

object ImplicitContext extends Preprocessor.Factory[ImplicitContext] {
  def apply[C <: blackbox.Context](c: C) = new ImplicitContext(c)
}

class ImplicitContext[C <: blackbox.Context](val c: C) extends Preprocessor[C] {
  import c.universe._

  def process(tree: Tree): Tree = {
    def processImplicitContext(tree: Apply): Option[Tree] = tree match {
      case Apply(_, List(Function(List(arg), _))) if arg.mods hasFlag Flag.IMPLICIT =>
        Some(tree)

      case Apply(fun, List(arg)) =>
        val valDef = internal.setPos(
          ValDef(Modifiers(Flag.IMPLICIT | Flag.PARAM), TermName("$bang"), TypeTree(), EmptyTree),
          arg.pos)

        val function = internal.setPos(Function(List(valDef), arg), arg.pos)

        Some(treeCopy.Apply(tree, fun, List(function)))

      case _ =>
        None
    }

    def processBlock(tree: Tree): Option[Tree] = {
      def blockPrefix(expr: Tree) = expr match {
        case q"on[..$_](...$_).run" => true
        case q"language.on[..$_](...$_).run" => true
        case q"loci.language.on[..$_](...$_).run" => true
        case q"${termNames.ROOTPKG}.loci.language.on[..$_](...$_).run" => true
        case q"on[..$_].apply(...$_).run" => true
        case q"language.on[..$_].apply(...$_).run" => true
        case q"loci.language.on[..$_].apply(...$_).run" => true
        case q"${termNames.ROOTPKG}.loci.language.on[..$_].apply(...$_).run" => true
        case q"on[..$_](...$_).run.capture(...$_)" => true
        case q"language.on[..$_](...$_).run.capture(...$_)" => true
        case q"loci.language.on[..$_](...$_).run.capture(...$_)" => true
        case q"${termNames.ROOTPKG}.loci.language.on[..$_](...$_).run.capture(...$_)" => true
        case q"on[..$_].apply(...$_).run.capture(...$_)" => true
        case q"language.on[..$_].apply(...$_).run.capture(...$_)" => true
        case q"loci.language.on[..$_].apply(...$_).run.capture(...$_)" => true
        case q"${termNames.ROOTPKG}.loci.language.on[..$_].apply(...$_).run.capture(...$_)" => true
        case _ => false
      }

      def blockExpr(expr: Tree) = expr match {
        case q"$expr.$name[..$_]" if blockPrefix(expr) =>
          val str = name.toString
          str == "apply" || str == "sbj"

        case _ =>
          blockPrefix(expr)
      }

      tree match {
        case tree @ Apply(fun, _) if blockExpr(fun) =>
          processImplicitContext(tree)

        case Apply(fun @ Apply(_, _), args) =>
          processBlock(fun) map { treeCopy.Apply(tree, _, args) }

        case _ =>
          None
      }
    }

    def processValues(tree: Tree): Option[Tree] = {
      def onPrefix(expr: Tree) = expr match {
        case q"on[..$_]" => true
        case q"language.on[..$_]" => true
        case q"loci.language.on[..$_]" => true
        case q"${termNames.ROOTPKG}.loci.language.on[..$_]" => true
        case _ => false
      }

      def placedPrefix(expr: Tree) = expr match {
        case q"placed" => true
        case q"language.placed" => true
        case q"loci.language.placed" => true
        case q"${termNames.ROOTPKG}.loci.language.placed" => true
        case _ => false
      }

      def placedExpr(expr: Tree) = expr match {
        case q"$expr.$name[..$_]" if onPrefix(expr) =>
          val str = name.toString
          str == "apply" || str == "local" || str == "sbj"

        case q"$expr.$name[..$_]" if placedPrefix(expr) =>
          name.toString == "apply"

        case _ =>
          onPrefix(expr) || placedPrefix(expr)
      }

      tree match {
        case Apply(fun @ Apply(_, _), args) =>
          processValues(fun) map { treeCopy.Apply(tree, _, args) }

        case Apply(select @ Select(qualifier, TermName("and")), List(arg)) =>
          processValues(qualifier) flatMap { qualifier =>
            processValues(arg) map { arg =>
              treeCopy.Apply(tree, treeCopy.Select(select, qualifier, TermName("and")), List(arg))
            }
          }

        case tree @ Apply(fun, _) if placedExpr(fun) =>
          processImplicitContext(tree)

        case _ =>
          None
      }
    }

    def processPlacementType(tpt: Tree, tree: Tree): Option[Tree] = {
      val explicitPlacementType = tpt match {
        case tq"on[..$_]" => true
        case tq"language.on[..$_]" => true
        case tq"loci.language.on[..$_]" => true
        case tq"${termNames.ROOTPKG}.loci.language.on[..$_]" => true
        case _ => false
      }

      if (explicitPlacementType && tree.nonEmpty) {
        val root = internal.setPos(Ident(termNames.ROOTPKG), tree.pos)
        val loci = internal.setPos(Select(root, TermName("loci")), tree.pos)
        val language = internal.setPos(Select(loci, TermName("language")), tree.pos)
        val placed = internal.setPos(Select(language, TermName("placed")), tree.pos)
        processImplicitContext(internal.setPos(Apply(placed, List(tree)), tree.pos))
      }
      else
        None
    }

    def processStats(stats: List[Tree]): List[Tree] = stats map {
      case tree @ DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
        treeCopy.DefDef(
          tree, mods, name, tparams, vparamss, tpt,
          processValues(rhs) orElse processPlacementType(tpt, rhs) getOrElse rhs)

      case tree @ ValDef(mods, name, tpt, rhs) =>
        treeCopy.ValDef(
          tree, mods, name, tpt,
          processValues(rhs) orElse processPlacementType(tpt, rhs) getOrElse rhs)

      case tree =>
        processValues(tree) getOrElse tree
    }

    object transformer extends Transformer {
      override def transform(tree: Tree): Tree = tree match {
        case ClassDef(mods, name, tparams, impl @ Template(parents, self, body)) =>
          super.transform(treeCopy.ClassDef(
            tree, mods, name, tparams, treeCopy.Template(
              impl, parents, self, processStats(body))))

        case ModuleDef(mods, name, impl @ Template(parents, self, body)) =>
          super.transform(treeCopy.ModuleDef(
            tree, mods, name, treeCopy.Template(
              impl, parents, self, processStats(body))))

        case _ =>
          super.transform(processBlock(tree) getOrElse tree)
      }
    }

    if ((c inferImplicitValue typeOf[feature.ManualImplicitContext]).isEmpty)
      transformer transform tree
    else
      tree
  }
}
