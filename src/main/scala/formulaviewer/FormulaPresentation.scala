package formulaviewer

import de.unruh.isabelle.pure.{Abs, App, Const, Context, Term, Typ}
import formulaviewer.Formula.{AppMulti, Numeral}
import formulaviewer.FormulaRenderer.{hbox, vbox}

import java.awt.{Color, Component}
import javax.swing.{BorderFactory, Box, BoxLayout, JComponent, JLabel, JSeparator, SwingConstants}
import scala.collection.mutable.ListBuffer

class FormulaPresentation(renderer: FormulaRenderer, level: Int, children: Seq[FormulaPresentation]) {
  assert(renderer.check(children))
  def swing: Component = renderer.swing(level, children)
}

object FormulaPresentation {
  def apply(renderer: FormulaRenderer, level: Int, children: FormulaPresentation*): FormulaPresentation = new FormulaPresentation(renderer, level, children)

  def fromIsabelle(formula: Formula): FormulaPresentation = fromIsabelle(formula.term, 0)(formula.context)

  def fromIsabelle(term: Term, level: Int)(implicit context: Context): FormulaPresentation = term match {
    case App(App(Const("HOL.eq", _), t), u) =>
      FormulaPresentation(InfixFormulaRenderer("="), level, fromIsabelle(t, level+1), fromIsabelle(u, level+1))
    case App(App(Const("Rings.divide_class.divide", _), t), u) =>
      FormulaPresentation(FractionRenderer, level, fromIsabelle(t, level + 1), fromIsabelle(u, level + 1))
    case Numeral(num) =>
      FormulaPresentation(IntegerRenderer(num), level)
    case AppMulti(terms @ _*) =>
      FormulaPresentation(ApplicationRenderer, level, terms.map(fromIsabelle(_, level+1)) : _*)
    case Abs(name, typ, body) =>
      FormulaPresentation(AbstractionRenderer(name,typ), level, fromIsabelle(body, level+1))
    case _ =>
      FormulaPresentation(FallbackRenderer(term.pretty(context)), level)
  }
}

abstract class FormulaRenderer {
  def check(children: Seq[FormulaPresentation]): Boolean
  def swing(level: Int, children: Seq[FormulaPresentation]): Component

  def touchup(level: Int, component: JComponent): Component = {
    component.setBackground(if (level%2 == 0) Color.white else Color.lightGray)
    component.setOpaque(true)
    val border = BorderFactory.createEmptyBorder(2,2,2,2)
    component.setBorder(border)
    component
  }
}

object FormulaRenderer {
  def hbox(stuff: AnyRef*): Box = box(BoxLayout.X_AXIS, stuff :_*)
  def vbox(stuff: AnyRef*): Box = box(BoxLayout.Y_AXIS, stuff :_*)
  def box(axis: Int, stuff: AnyRef*): Box = {
    val box = new Box(axis)
    for (thing <- stuff)
      thing match {
        case pres : FormulaPresentation =>
          box.add(pres.swing)
        case str : String =>
          box.add(new JLabel(str))
        case component: Component =>
          box.add(component)
      }
    box
  }
}

case class InfixFormulaRenderer(operation: String) extends FormulaRenderer {
  override def swing(level: Int, children: Seq[FormulaPresentation]): Component = {
    val Seq(left,right) = children
    touchup(level, hbox(left, operation, right))
  }

  override def check(children: Seq[FormulaPresentation]): Boolean =
    children.length == 2
}

case object ApplicationRenderer extends FormulaRenderer {
  override def check(children: Seq[FormulaPresentation]): Boolean = children.nonEmpty

  override def swing(level: Int, children: Seq[FormulaPresentation]): Component = {
    val Seq(head, args @_*) = children
    val result = ListBuffer[AnyRef]()
    result += head
    result += "("
    var first = true
    for (arg <- args) {
      if (!first) result += ","
      result += arg
      first = false
    }
    result += ")"
    touchup(level, hbox(result.toSeq : _*))
  }
}

case class AbstractionRenderer(name: String, typ: Typ) extends FormulaRenderer {
  override def check(children: Seq[FormulaPresentation]): Boolean = children.lengthIs == 1

  override def swing(level: Int, children: Seq[FormulaPresentation]): Component = {
    touchup(level, hbox(s"λ$name.", children.head))
  }
}

case class FallbackRenderer(string: String) extends FormulaRenderer {
  override def check(children: Seq[FormulaPresentation]): Boolean = children.isEmpty

  override def swing(level: Int, children: Seq[FormulaPresentation]): Component =
    touchup(level, new JLabel(string))
}

case class IntegerRenderer(num: BigInt) extends FormulaRenderer {
  override def check(children: Seq[FormulaPresentation]): Boolean = children.isEmpty

  override def swing(level: Int, children: Seq[FormulaPresentation]): Component =
    touchup(level, new JLabel(num.toString))
}

object FractionRenderer extends FormulaRenderer {
  override def check(children: Seq[FormulaPresentation]): Boolean = children.lengthIs == 2

  override def swing(level: Int, children: Seq[FormulaPresentation]): Component = {
    val Seq(nominator, denominator) = children
    vbox(nominator, new JSeparator(SwingConstants.HORIZONTAL), denominator)
  }
}
