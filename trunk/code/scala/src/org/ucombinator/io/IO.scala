package org.ucombinator.scala.io ;


/**
 Convenient IO methods.
 */
object IO {
  
  def writeTo (file : String, contents : String) {
    val out = new java.io.BufferedWriter(new java.io.FileWriter(file)) 
    out.write(contents) 
    out.flush() 
    out.close() 
  }

}
