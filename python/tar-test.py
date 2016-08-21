import tarfile
import big_file


big_file.create_big_file()
tar = tarfile.open("big_file.tar.gz", "w|gz")
tar.add("big_file.txt")
tar.close()


