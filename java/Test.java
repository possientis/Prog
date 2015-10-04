import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Test {


  public static void main(String[] args) throws IOException {

    int[] myArr = new int[5];
    int[][] matrix = new int[2][3];

    for(int i = 0; i < 2; ++i)
      for(int j = 0; j < 3; ++j){

        matrix[i][j] = i+j;
        System.out.println(matrix[i][j]);
      }

  }
}
