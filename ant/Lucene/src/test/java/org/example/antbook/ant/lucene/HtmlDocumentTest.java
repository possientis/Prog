package org.example.antbook.ant.lucene;

import java.io.IOException;
import java.io.File;
import junit.framework.TestCase;

public class HtmlDocumentTest extends DocumentTestCase
{
  public HtmlDocumentTest (String name) {
    super(name);
  }

  HtmlDocument doc;

  public void setUp() throws IOException {
    System.err.println("\nsetUp is running");
//    doc = new HtmlDocument(getFile("test.html"));
  }

  public void testDoc() {
    System.err.println("testDoc is running");
//    assertEquals("Test1", true, false);
//    assertEquals("Title", "Test Title", doc.getTitle());
//    assertEquals("Body", "This is some test", doc.getBodyText());

  }

  public void tearDown() {
    System.err.println("tearDown is running");
    doc = null;
  }

}
