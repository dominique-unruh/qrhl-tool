package formulaviewer

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.control.Isabelle.Setup
import de.unruh.isabelle.pure.Context
import formulaviewer.FormulaViewer.logger
import org.log4s

import java.awt.{BorderLayout, Component, Point}
import java.awt.event.{ActionEvent, MouseAdapter, MouseEvent}
import java.nio.file.Path
import javax.swing.JOptionPane.{ERROR_MESSAGE, showMessageDialog}
import javax.swing._
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}
import scala.util.control.Breaks.{break, breakable}

class FormulaViewer extends JFrame("qrhl-tool formula viewer") with ContextMapProvider {
  private val listModel = new DefaultListModel[Formula]()
  private val formulaList: JList[Formula] = new JList[Formula](listModel)
  private val statusBar = new JLabel()
  private val differ = new Differ
  private val leftFormula = new FormulaWidget(this, Differ.Side(differ, side = true))
  private val rightFormula = new FormulaWidget(this, Differ.Side(differ, side = false))

  private var _contextMap : ContextMap = ContextMap.id
  private var context: Context = _
  private var isabelle: Isabelle = _

  private val contextOptions: Seq[ContextOption] = Seq(
    ContextOptionToggle("Show types", "Config.put Printer.show_types false ctxt", "Config.put Printer.show_types true ctxt"),
    ContextOptionToggle("Show sorts", "Config.put Printer.show_sorts false ctxt", "Config.put Printer.show_sorts true ctxt"),
    ContextOptionToggle("Show brackets", "Config.put Printer.show_brackets false ctxt", "Config.put Printer.show_brackets true ctxt")
  )

  init()

  def contextMap: ContextMap = _contextMap

  object formulaListPopup extends JPopupMenu {
    add(new SimpleAction("To left", e =>
      showFormulaLeft(formulaList.getSelectedValue)
    ))
    add(new SimpleAction("To right", e =>
      showFormulaRight(formulaList.getSelectedValue)
    ))
    add(new SimpleAction("Delete", e =>
      for (index <- formulaList.getSelectedIndices.reverse) {
        logger.debug(s"Remove $index")
        listModel.remove(index)
      }
    ))

    override def show(invoker: Component, x: Int, y: Int): Unit = {
      val itemIdx = formulaList.locationToIndex(new Point(x,y))
      if (itemIdx != -1) {
        if (!formulaList.isSelectedIndex(itemIdx))
          formulaList.setSelectedIndex(itemIdx)
      }
      super.show(invoker, x, y)
    }
  }

  def setContext(isabelle: Isabelle, context: Context): Unit = synchronized {
    val firstIsabelle = this.isabelle eq null
    this.isabelle = isabelle
    this.context = context
    if (firstIsabelle) {
      for (option <- contextOptions)
        option.setIsabelle(isabelle)
      updateContextMap()
    }
  }

  object listMouseListener extends MouseAdapter {
    // TODO remove
    override def mouseClicked(e: MouseEvent): Unit =
      if (e.getClickCount == 2) {
        val index = formulaList.locationToIndex(e.getPoint)
        val formula = listModel.getElementAt(index)
        showFormulaLeft(formula)
        e.consume()
      }
  }

  def addFormula(formula: Formula): Unit =
    listModel.add(0, formula)

  def showFormulaLeft(formula: Formula): Unit = {
    leftFormula.showFormula(formula)
    rightFormula.repaint()
    statusBar.setText("")
  }

  def showFormulaRight(formula: Formula): Unit = {
    rightFormula.showFormula(formula)
    leftFormula.repaint()
    statusBar.setText("")
  }

  object addFormulaAction extends AbstractAction("Input formula") {
    override def actionPerformed(e: ActionEvent): Unit = breakable {
      implicit val isabelle: Isabelle = FormulaViewer.this.isabelle
      implicit val context: Context = FormulaViewer.this.context
      if (context == null) {
        showMessageDialog(FormulaViewer.this, "Isabelle not initialized", "Error", ERROR_MESSAGE)
        break()
      }
      statusBar.setText("")
      val string = JOptionPane.showInputDialog(FormulaViewer.this, "Formula:", "Add formula", JOptionPane.PLAIN_MESSAGE)
      if (string == null) break()
      val formula = try
        Formula.fromString(string)
      catch {
        case e: Throwable =>
          showMessageDialog(FormulaViewer.this, s"Adding message failed:\n$e", "Error", ERROR_MESSAGE)
          break()
      }
      addFormula(formula)
    }
  }

  private class FormulaToCollectionAction(widget: FormulaWidget) extends AbstractAction("To collection") {
    override def actionPerformed(e: ActionEvent): Unit = {
      for (formula <- widget.selectedSubformulas)
        addFormula(formula)
    }
  }

  def updateContextMap(): Unit = {
    var newContextMap = _contextMap
    for (option <- contextOptions)
      newContextMap = newContextMap * option.contextMap
    _contextMap = newContextMap
    leftFormula.contextMapChanged()
    rightFormula.contextMapChanged()
  }

  private def init(): Unit = {
    val formulaListScroll = new JScrollPane(formulaList)
    val formulaSplit = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, leftFormula, rightFormula)
    formulaSplit.setOneTouchExpandable(true)
    formulaSplit.setDividerLocation(.5d)
    val split = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, formulaSplit, formulaListScroll)
    split.setOneTouchExpandable(true)
    split.setDividerLocation(.8d)

    getContentPane.add(split, BorderLayout.CENTER)
    getContentPane.add(statusBar, BorderLayout.SOUTH)
    val toolbar = new JToolBar()
    getContentPane.add(toolbar, BorderLayout.NORTH)

    toolbar.add(addFormulaAction)
    for (option <- contextOptions) {
      toolbar.add(option.button)
      option.addListener { () => updateContextMap() }
    }

    differ.left = leftFormula
    differ.right = rightFormula

    leftFormula.addPopupAction(new FormulaToCollectionAction(leftFormula))
    rightFormula.addPopupAction(new FormulaToCollectionAction(rightFormula))

    formulaList.setComponentPopupMenu(formulaListPopup)

    setSize(1000, 800)
    setDefaultCloseOperation(WindowConstants.HIDE_ON_CLOSE)

    formulaList.addMouseListener(listMouseListener)
  }
}

object FormulaViewer {
  private val logger = log4s.getLogger

  def main(args: Array[String]): Unit = {
    implicit val executionContext: ExecutionContextExecutor = ExecutionContext.global
    val setup = Setup(isabelleHome = Path.of("c:\\temp\\Isabelle"))
    implicit val isabelle: Isabelle = new Isabelle(setup)
    implicit val context: Context = Context("Main")

    val viewer = new FormulaViewer
    viewer.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE)
    viewer.setVisible(true)
    isabelle.await
    viewer.setContext(isabelle, context)

    val initialFormulas: Seq[Formula] = Seq(
        Formula.fromString("1+(2) :: nat"),
        Formula.fromString("A ==> B ==> (!!C. A == (B & C))")
      )
    for (formula <- initialFormulas)
      viewer.addFormula(formula)
    viewer.showFormulaLeft(initialFormulas.head)
  }
}


class SimpleAction(name: String, handler: ActionEvent => Unit) extends AbstractAction(name: String) {
  override def actionPerformed(e: ActionEvent): Unit = handler(e)
}