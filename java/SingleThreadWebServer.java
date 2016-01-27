import java.io.*;
import java.net.*;


class SingleThreadWebServer {
  public static void main(String[] args) throws IOException {
    ServerSocket socket = new ServerSocket(80);
    while (true) {
      Socket connection = socket.accept();
      handleRequest(connection);
    }
  }

  private static void handleRequest(Socket connection){
  }
}
