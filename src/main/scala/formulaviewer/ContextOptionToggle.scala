package formulaviewer

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.Context

import java.awt.event.ActionEvent
import javax.swing.{AbstractAction, JCheckBox}
import scala.collection.mutable

case class ContextOptionToggle(title: String, deactivate: String, activate: String) extends ContextOption {
  private implicit var isabelle: Isabelle = _
  private lazy val activateML = MLValue.compileFunction[Context, Context](s"fn ctxt => ( $activate )")
  private lazy val deactivateML = MLValue.compileFunction[Context, Context](s"fn ctxt => ( $deactivate )")
  private var _active = false

  def setIsabelle(isabelle: Isabelle): Unit =
    this.isabelle = isabelle

  def active: Boolean = _active

  private val listeners: mutable.ArrayDeque[() => ()] = new mutable.ArrayDeque

  def addListener(listener: () => ()): Unit =
    synchronized {
      listeners += listener
    }

  def setActive(active: Boolean): Unit = {
    _active = active
    for (listener <- listeners)
      listener()
  }

  def toggleActive(): Unit = setActive(!active)

  def contextMap: ContextMap = {
    if (isabelle != null) {
      activateML.await;
      deactivateML.await // Force errors early
      new ContextMap(ctxt => (if (active) activateML else deactivateML)(ctxt).retrieveNow)
    } else
      ContextMap.id
  }

  object action extends AbstractAction(title) {
    override def actionPerformed(e: ActionEvent): Unit = {
      toggleActive()
    }
  }

  def button: JCheckBox = {
    val button = new JCheckBox(title, active)
    button.setAction(action)
    button
  }
}
