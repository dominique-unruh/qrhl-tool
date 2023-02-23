package formulaviewer

import formulaviewer.FormulaTreeNode.logger
import org.log4s

import java.util
import javax.swing.tree.TreeNode
import scala.jdk.CollectionConverters.IteratorHasAsJava

class FormulaTreeNode(contextMapProvider: ContextMapProvider, val parent: FormulaTreeNode, val formula: Formula) extends TreeNode {
  lazy val myChildren: List[FormulaTreeNode] = formula.children.map(new FormulaTreeNode(contextMapProvider, this, _))

  private var lastRender: (ContextMap, String) = (new ContextMap(_ => throw new Exception()), "")

  override def toString: String = {
    val contextMap = contextMapProvider.contextMap
    if (contextMap same lastRender._1) lastRender._2
    else {
      val string = formula.descriptiveString(contextMap)
      logger.debug(s"Rendered formula ${System.identityHashCode(this)}: $string")
      lastRender = (contextMap, string)
      string
    }
  }

  override def getChildAt(childIndex: Int): FormulaTreeNode = myChildren(childIndex)

  override def getChildCount: Int = myChildren.length

  override def getParent: TreeNode = parent

  override def getIndex(node: TreeNode): Int = myChildren.indexOf(node)

  override def getAllowsChildren: Boolean = true

  override def isLeaf: Boolean = myChildren.isEmpty

  override def children(): util.Enumeration[_ <: FormulaTreeNode] = myChildren.iterator.asJavaEnumeration
}

object FormulaTreeNode {
  private val logger = log4s.getLogger
}