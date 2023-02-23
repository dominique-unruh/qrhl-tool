package formulaviewer

class FakeFormulaTreeNode(formulaViewer: FormulaViewer, text: String) extends FormulaTreeNode(formulaViewer, null, null) {
  override lazy val myChildren: List[Nothing] = Nil

  override def toString: String = text
}
