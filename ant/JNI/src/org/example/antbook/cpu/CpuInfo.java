package org.example.antbook.cpu;

public class CpuInfo {

  native long getCpuClock();

  static {
    System.loadLibrary("CpuInfo");
  }

}
