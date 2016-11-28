package org.example.antbook;

import org.example.antbook.common.Document;
import org.example.antbook.common.SearchUtil;

public class Search {
  public static void main(String args[]) throws Exception {
    if(args.length!=2) {
      System.out.println("search: index searchterm");
      System.exit(-1);
    }

    SearchUtil.init(args[0]);

    Document[] docs = SearchUtil.findDocuments(args[1]);

    for (int i=0; i < docs.length; ++i) {
      System.out.println((i + 1) + ": "
          + docs[i].getField("path"));
    }
    
    System.out.println("files found: " + docs.length);
  }
}
