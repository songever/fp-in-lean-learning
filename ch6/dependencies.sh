export LEAN_PATH=".:./utils"

for file in ./utils/*.lean; do
  [ -e "$file" ] || continue
  filename=$(basename "$file" .lean)
  lean -o "./${filename}.olean" "$file"
done