import java.io.IOException;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;
var exts = Stream.of("rkt", "md", "tex", "m", "v", "c").collect(Collectors.toMap(Function.identity(), o -> new ArrayList<String>()));
var target = Paths.get("files");
if (Files.notExists(target)) Files.createDirectory(target);
Files.walkFileTree(target, new SimpleFileVisitor<>() {
  @Override
  public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
    if (attrs.isRegularFile()) Files.deleteIfExists(file);
    return FileVisitResult.CONTINUE;
  }
});
Files.walkFileTree(Paths.get("."), new SimpleFileVisitor<>() {
  @Override
  public FileVisitResult visitFile(Path p, BasicFileAttributes attrs) throws IOException {
    var fileName = p.toString();
    var ext = fileName.substring(fileName.lastIndexOf('.') + 1);
    if (!exts.containsKey(ext)) return FileVisitResult.CONTINUE;
    var content = Files.readString(p)
        .replaceAll("yqz5714", "")
        .replaceAll("(Stat|Math|Cmpsc|Cmpen)\\d+", "")
        .replaceAll("\r", "")
        .replaceAll("Tesla[()\\w ]+Zhang", "")
        .replaceAll("Yinsen[()\\w ]+Zhang", "");
    exts.get(ext).addAll(List.of(content.split("\\R\\R+")));
    return FileVisitResult.CONTINUE;
  }
})
for (var entry : exts.entrySet()) {
  var ext = entry.getKey();
  var v = entry.getValue();
  Collections.sort(v);
  var content = String.join("\n\n", new HashSet<>(v));
  var newPath = Paths.get("files", "assembly.%s".formatted(ext));
  System.out.println(newPath + ": " + content.length());
  Files.writeString(newPath, content, StandardOpenOption.CREATE_NEW, StandardOpenOption.WRITE);
}
/exit