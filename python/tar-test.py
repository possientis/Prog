import tarfile
import big_file


big_file.create_big_file()
tar = tarfile.open("big_file.tar", "w")
tar.add("big_file.txt")
tar.close()


