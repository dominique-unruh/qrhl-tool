package formulaviewer

import javax.swing.tree.{DefaultTreeModel, TreePath}
import javax.swing.{JPanel, JScrollPane, JSplitPane, JTree}

class FormulaWidget(contextMapProvider: ContextMapProvider) extends JSplitPane(JSplitPane.VERTICAL_SPLIT) {
  private val treeModel = new DefaultTreeModel(new FakeFormulaTreeNode(contextMapProvider, "<nothing loaded>"))
  private val tree: JTree = new JTree(treeModel)
  private val formulaPane = new JPanel()

  init()

  def init(): Unit = {
    val treeScroll = new JScrollPane(tree)
    val formulaPaneScroll = new JScrollPane(formulaPane)
    setLeftComponent(treeScroll)
    setRightComponent(formulaPaneScroll)
    setOneTouchExpandable(true)
  }

  def contextMapChanged(): Unit = {
    for (node <- allTreeNodes())
      treeModel.nodeChanged(node)
  }

  private def allTreeNodes(node: FormulaTreeNode = treeModel.getRoot.asInstanceOf[FormulaTreeNode]): IterableOnce[FormulaTreeNode] = {
    val subnodes =
      for (child <- node.myChildren.iterator;
           node <- allTreeNodes(child))
      yield node
    Iterator(node) ++ subnodes
  }

  def selectedSubformulas: Seq[Formula] = {
    val paths = tree.getSelectionModel.getSelectionPaths
    val paths2 = if (paths.isEmpty) Array(new TreePath(treeModel.getRoot)) else paths
    for (path <- paths2.toSeq;
         formula = path.getLastPathComponent.asInstanceOf[FormulaTreeNode]
         if !formula.isInstanceOf[FakeFormulaTreeNode])
    yield formula.formula
  }

  def showFormula(formula: Formula): Unit = {
    treeModel.setRoot(new FormulaTreeNode(contextMapProvider, null, formula))
    formulaPane.removeAll()
    formulaPane.add(FormulaPresentation.fromIsabelle(formula).swing)
    formulaPane.revalidate()
  }
}
