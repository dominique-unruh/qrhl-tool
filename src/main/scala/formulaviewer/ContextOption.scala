package formulaviewer

import de.unruh.isabelle.control.Isabelle

import java.awt.Component
import javax.swing.Action

abstract class ContextOption {
  def contextMap: ContextMap

  def button: Component

  def addListener(listener: () => ()): Unit

  val action: Action

  /** Must not be called more than once. */
  def setIsabelle(isabelle: Isabelle): Unit
}
