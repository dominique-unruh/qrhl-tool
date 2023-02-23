package formulaviewer

import java.awt.Color

class Differ {
  var left: FormulaWidget = _
  var right: FormulaWidget = _

  private def other(side: Boolean) = if (side) right else left
  private def selected(side: Boolean) = if (side) left else right

  // TODO cache this
  def color(side: Boolean, path: List[Int]): Color = {
    val selectedFormula = selected(side).formulaAt(path).get
    val otherFormula = other(side).formulaAt(path)

    otherFormula match {
      case Some(otherFormula) =>
        if (selectedFormula.term == otherFormula.term)
          Color.green
        else
          Color.red
      case None =>
        Color.lightGray
    }
  }
}

object Differ {
  case class Side(differ: Differ, side: Boolean) {
    def color(path: List[Int]): Color = differ.color(side, path)
  }
}