#!/bin/sh
# Build the .deb package with only dpkg-deb (no debhelper needed).
#
#   ./build-deb.sh            ->  dist/playlist-checker_<version>_all.deb
#
# The version comes from APP_VERSION in playlist_checker_gui.py and must match
# the first entry of debian/changelog. Package fields (dependencies,
# description, maintainer) are read from debian/control, so that file is the
# only place to edit them.
set -eu
cd "$(dirname "$0")"
umask 022

PKG=playlist-checker

# ---------------------------------------------------------------- checks
for tool in dpkg-deb gzip md5sum awk sed; do
    command -v "$tool" >/dev/null 2>&1 || { echo "error: '$tool' is missing (sudo apt install dpkg-dev)" >&2; exit 1; }
done

VERSION=$(sed -n 's/^APP_VERSION = "\([^"]*\)".*/\1/p' playlist_checker_gui.py)
CHANGELOG_VERSION=$(sed -n '1s/^[^(]*(\([^)]*\)).*/\1/p' debian/changelog)
[ -n "$VERSION" ] || { echo "error: APP_VERSION not found in playlist_checker_gui.py" >&2; exit 1; }
if [ "$VERSION" != "$CHANGELOG_VERSION" ]; then
    echo "error: version mismatch - program says $VERSION, debian/changelog says $CHANGELOG_VERSION" >&2
    echo "       change APP_VERSION or add a new entry to debian/changelog (dch -v $VERSION)" >&2
    exit 1
fi

APP_URL=$(sed -n 's/^PROJECT_URL = "\([^"]*\)".*/\1/p' playlist_checker_gui.py)
PKG_URL=$(sed -n 's/^Homepage: *//p' debian/control | head -n 1)
if [ -n "$PKG_URL" ] && [ "$APP_URL" != "$PKG_URL" ]; then
    echo "error: project address differs - program: $APP_URL, debian/control Homepage: $PKG_URL" >&2
    exit 1
fi

EMPTY=$(find . -type f -size 0 -not -path "./build/*" -not -path "./dist/*" -not -path "./.git/*")
if [ -n "$EMPTY" ]; then
    echo "error: these files are empty:" >&2
    echo "$EMPTY" >&2
    exit 1
fi

if command -v python3 >/dev/null 2>&1; then
    python3 -m py_compile playlist_checker_gui.py || { echo "error: playlist_checker_gui.py has a syntax error" >&2; exit 1; }
    rm -rf __pycache__
fi

# ---------------------------------------------------------------- files
ROOT=build/root
rm -rf build
mkdir -p "$ROOT/DEBIAN" dist

install -Dm755 playlist_checker_gui.py  "$ROOT/usr/share/$PKG/playlist_checker_gui.py"
install -Dm755 bin/playlist-checker     "$ROOT/usr/bin/playlist-checker"
install -Dm644 data/playlist-checker.desktop "$ROOT/usr/share/applications/playlist-checker.desktop"
for dir in data/icons/*x*; do
    size=$(basename "$dir")
    install -Dm644 "$dir/playlist-checker.png" "$ROOT/usr/share/icons/hicolor/$size/apps/playlist-checker.png"
done
install -Dm644 data/icons/scalable/playlist-checker.svg "$ROOT/usr/share/icons/hicolor/scalable/apps/playlist-checker.svg"
# fallback location, used when the icon theme or its cache can't be used
install -Dm644 data/icons/128x128/playlist-checker.png "$ROOT/usr/share/pixmaps/playlist-checker.png"
install -d "$ROOT/usr/share/man/man1" "$ROOT/usr/share/doc/$PKG"
gzip -9n -c data/playlist-checker.1 > "$ROOT/usr/share/man/man1/playlist-checker.1.gz"
gzip -9n -c debian/changelog       > "$ROOT/usr/share/doc/$PKG/changelog.gz"
install -m644 debian/copyright "$ROOT/usr/share/doc/$PKG/copyright"
install -Dm644 data/url-list-example.txt "$ROOT/usr/share/doc/$PKG/examples/url-list-example.txt"
chmod 644 "$ROOT/usr/share/man/man1/playlist-checker.1.gz" "$ROOT/usr/share/doc/$PKG/changelog.gz"

# ---------------------------------------------------------------- DEBIAN/control (from debian/control)
get() { sed -n "s/^$1: *//p" debian/control | head -n 1; }
MAINTAINER=$(get Maintainer)
SECTION=$(get Section)
PRIORITY=$(get Priority)
DEPENDS=$(get Depends | sed 's/\${misc:Depends}, *//; s/, *\${misc:Depends}//')
RECOMMENDS=$(get Recommends)
SUGGESTS=$(get Suggests)
HOMEPAGE=$(get Homepage)
DESCRIPTION=$(awk '/^Description:/ {p=1; print; next} p && /^ / {print; next} p {exit}' debian/control)
INSTALLED_SIZE=$(du -sk --apparent-size "$ROOT/usr" | cut -f1)

{
    echo "Package: $PKG"
    echo "Version: $VERSION"
    echo "Architecture: all"
    echo "Maintainer: $MAINTAINER"
    echo "Installed-Size: $INSTALLED_SIZE"
    echo "Depends: $DEPENDS"
    [ -n "$RECOMMENDS" ] && echo "Recommends: $RECOMMENDS"
    [ -n "$SUGGESTS" ] && echo "Suggests: $SUGGESTS"
    echo "Section: $SECTION"
    echo "Priority: $PRIORITY"
    [ -n "$HOMEPAGE" ] && echo "Homepage: $HOMEPAGE"
    echo "$DESCRIPTION"
} > "$ROOT/DEBIAN/control"

(cd "$ROOT" && find usr -type f -print0 | sort -z | xargs -0 md5sum) > "$ROOT/DEBIAN/md5sums"
chmod 644 "$ROOT/DEBIAN/control" "$ROOT/DEBIAN/md5sums"

# maintainer scripts (the #DEBHELPER# marker is only for dpkg-buildpackage)
for script in preinst postinst prerm postrm; do
    if [ -f "debian/$script" ]; then
        sed '/^#DEBHELPER#$/d' "debian/$script" > "$ROOT/DEBIAN/$script"
        chmod 755 "$ROOT/DEBIAN/$script"
    fi
done

# ---------------------------------------------------------------- build
DEB="dist/${PKG}_${VERSION}_all.deb"
dpkg-deb --root-owner-group -Zxz --build "$ROOT" "$DEB" >/dev/null
echo "Built: $DEB ($(du -h "$DEB" | cut -f1))"

if command -v lintian >/dev/null 2>&1; then
    echo "Running lintian..."
    lintian --info "$DEB" || true
fi

echo
echo "Install:    sudo apt install ./$DEB"
echo "Uninstall:  sudo apt remove $PKG"
