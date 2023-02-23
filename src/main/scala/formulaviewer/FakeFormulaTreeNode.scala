package formulaviewer

class FakeFormulaTreeNode(contextMapProvider: ContextMapProvider, text: String) extends FormulaTreeNode(contextMapProvider, null, 0, null) {
  override lazy val myChildren: List[Nothing] = Nil

  override def toString: String = text

  override def formulaAt(path: List[Int]): Option[Formula] = None
}
