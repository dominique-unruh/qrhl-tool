package formulaviewer

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.control.Isabelle.Setup
import de.unruh.isabelle.pure.Context

import java.awt.BorderLayout
import java.awt.event.{ActionEvent, MouseAdapter, MouseEvent}
import java.nio.file.Path
import java.util
import javax.swing.tree.{DefaultTreeModel, TreeNode}
import javax.swing._
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}
import scala.jdk.CollectionConverters.IteratorHasAsJava
import scala.util.control.Breaks.{break, breakable}

class IsabelleFormulaViewer extends JFrame("Isabelle Formula Viewer") {
  private val listModel = new DefaultListModel[Formula]()
  private val formulaList: JList[Formula] = new JList[Formula](listModel)
  private val treeModel = new DefaultTreeModel(new FakeFormulaTreeNode("<nothing loaded>"))
  private val tree: JTree = new JTree(treeModel)
  private val statusBar = new JLabel()

  private var context: Context = _
  private var isabelle: Isabelle = _

  init()

  def setContext(isabelle: Isabelle, context: Context): Unit = {
    this.isabelle = isabelle
    this.context = context
  }

  object listMouseListener extends MouseAdapter {
    override def mouseClicked(e: MouseEvent): Unit =
      if (e.getClickCount == 2) {
        val index = formulaList.locationToIndex(e.getPoint)
        val formula = listModel.getElementAt(index)
        showFormula(formula)
        e.consume()
      }
  }

  def addFormula(formula: Formula): Unit =
    listModel.addElement(formula)

  def showFormula(formula: Formula): Unit = {
    treeModel.setRoot(new FormulaTreeNode(null, formula))
    statusBar.setText("")
  }

  object addFormulaAction extends AbstractAction("Add formula") {
    override def actionPerformed(e: ActionEvent): Unit = breakable {
      implicit val isabelle: Isabelle = IsabelleFormulaViewer.this.isabelle
      implicit val context: Context = IsabelleFormulaViewer.this.context
      if (context == null) {
        JOptionPane.showMessageDialog(IsabelleFormulaViewer.this, "Isabelle not initialized", "Error", JOptionPane.ERROR_MESSAGE)
        break
      }
      statusBar.setText("")
      val string = JOptionPane.showInputDialog(IsabelleFormulaViewer.this, "Formula:", "Add formula", JOptionPane.PLAIN_MESSAGE)
      if (string == null) break
      val formula = try
        Formula.fromString(string)
      catch {
        case e: Throwable =>
          JOptionPane.showMessageDialog(IsabelleFormulaViewer.this, s"Adding message failed:\n$e", "Error", JOptionPane.ERROR_MESSAGE)
          break
      }
      listModel.addElement(formula)
      showFormula(formula)
    }
  }

  private def init(): Unit = {
    val split = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT)
    split.setLeftComponent(tree)
    split.setRightComponent(formulaList)
    getContentPane.add(split, BorderLayout.CENTER)
    getContentPane.add(statusBar, BorderLayout.SOUTH)
    val toolbar = new JToolBar()
    getContentPane.add(toolbar, BorderLayout.NORTH)

    toolbar.add(addFormulaAction)

    setSize(1000, 800)
    setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE)

    formulaList.addMouseListener(listMouseListener)
  }

/*  def initialFormulas: Seq[Formula] = Seq(
    Formula.fromString("1+(2) :: nat"),
    Formula.fromString("A ==> B ==> (!!C. A == (B & C))")
  )*/
}

object IsabelleFormulaViewer {
/*  def main(args: Array[String]): Unit = {
    implicit val executionContext: ExecutionContextExecutor = ExecutionContext.global
    val setup = Setup(isabelleHome = Path.of("c:\\temp\\Isabelle"))
    implicit val isabelle: Isabelle = new Isabelle(setup)
    implicit val context: Context = Context("Main")

    val frame = new IsabelleFormulaViewer
    frame.setVisible(true)
  }*/
}



class FormulaTreeNode(val parent: FormulaTreeNode, val formula: Formula) extends TreeNode {
  lazy val myChildren: List[FormulaTreeNode] = formula.children.map(new FormulaTreeNode(this, _))

  override def toString: String = formula.toString
  override def getChildAt(childIndex: Int): TreeNode = myChildren(childIndex)
  override def getChildCount: Int = myChildren.length
  override def getParent: TreeNode = parent
  override def getIndex(node: TreeNode): Int = myChildren.indexOf(node)
  override def getAllowsChildren: Boolean = true
  override def isLeaf: Boolean = myChildren.isEmpty
  override def children(): util.Enumeration[_ <: TreeNode] = myChildren.iterator.asJavaEnumeration
}

class FakeFormulaTreeNode(text: String) extends FormulaTreeNode(null, null) {
  override lazy val myChildren: List[Nothing] = Nil

  override def toString: String = text
}

object FormulaTreeNode {
}
