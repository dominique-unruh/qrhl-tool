package formulaviewer

class FakeFormulaTreeNode(contextMapProvider: ContextMapProvider, text: String) extends FormulaTreeNode(contextMapProvider, null, null) {
  override lazy val myChildren: List[Nothing] = Nil

  override def toString: String = text
}
