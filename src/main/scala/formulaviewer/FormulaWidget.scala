package formulaviewer

import formulaviewer.FormulaWidget.logger
import org.jetbrains.annotations.NotNull
import org.log4s

import java.awt.{Color, Component}
import java.lang.AssertionError
import javax.swing.tree.{DefaultTreeCellRenderer, DefaultTreeModel, TreeCellRenderer, TreePath}
import javax.swing.{JPanel, JScrollPane, JSplitPane, JTree}


class FormulaWidget(contextMapProvider: ContextMapProvider, differSide: Differ.Side) extends JSplitPane(JSplitPane.VERTICAL_SPLIT) {
  private val treeModel = new DefaultTreeModel(new FakeFormulaTreeNode(contextMapProvider, "<nothing loaded>"))
  private val tree: JTree = new JTree(treeModel)
  private val formulaPane = new JPanel()

  init()

  def formulaAt(path: List[Int]): Option[Formula @NotNull] =
    treeModel.getRoot.asInstanceOf[FormulaTreeNode].formulaAt(path)

  def init(): Unit = {
    val treeScroll = new JScrollPane(tree)
    val formulaPaneScroll = new JScrollPane(formulaPane)
    setLeftComponent(treeScroll)
    setRightComponent(formulaPaneScroll)
    setOneTouchExpandable(true)
    tree.setCellRenderer(cellRenderer)
  }

  object cellRenderer extends DefaultTreeCellRenderer {
    override def getTreeCellRendererComponent(tree: JTree, value: Any, selected: Boolean, expanded: Boolean, leaf: Boolean, row: Int, hasFocus: Boolean): Component = {
      super.getTreeCellRendererComponent(tree, value, selected, expanded, leaf, row, hasFocus)
      value match {
        case _ : FakeFormulaTreeNode =>
        case node : FormulaTreeNode =>
          val path = node.path
          val color = differSide.color(path)
          setOpaque(true)
          setBackground(color)
        case _ =>
          throw new AssertionError(s"cell renderer got a ${value.getClass}")
      }
      this
    }
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

  def showFormula(@NotNull formula: Formula): Unit = {
    if (formula == null)
      throw new NullPointerException("formula == null")
    treeModel.setRoot(new FormulaTreeNode(contextMapProvider, null, 0, formula))
    formulaPane.removeAll()
    formulaPane.add(FormulaPresentation.fromIsabelle(formula).swing)
    formulaPane.revalidate()
  }
}

object FormulaWidget {
  private val logger = log4s.getLogger
}