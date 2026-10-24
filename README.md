# TV & Radio Playlist Checker

Desktop application for IPTV and internet-radio playlists (M3U, M3U8, PLS, XSPF,
also gzip-compressed `.m3u.gz` / `.m3u8.gz`): checks every stream, rechecks offline
ones, marks duplicates, manages groups and saves a clean playlist (logos, EPG and
player options kept).

Project page: https://github.com/antoxa78/PyPlaylist-Checker

## Folder contents

| Path | What it is |
|---|---|
| `playlist_checker_gui.py` | the program (single file, Python 3.9+ and Tk) |
| `bin/playlist-checker` | start command installed as `/usr/bin/playlist-checker` |
| `data/playlist-checker.desktop` | applications-menu entry (English + Hebrew) |
| `data/icons/*/playlist-checker.png`, `data/icons/scalable/playlist-checker.svg` | application icon, 16–512 px PNG and vector SVG |
| `data/playlist-checker.1` | manual page (`man playlist-checker`) |
| `data/url-list-example.txt` | example list of playlist addresses (File → Open list of playlist URLs) |
| `debian/` | Debian packaging: control, rules, changelog, copyright, install lists |
| `build-deb.sh` | builds the .deb with `dpkg-deb` only |
| `LICENSE` | MIT licence |

## Dependencies

* **Runtime** (installed automatically by apt): `python3 (>= 3.9)`, `python3-tk`
* **Recommended:** `vlc` or `mpv` (playing channels), `ffmpeg` (finds “not available in your country” banners by the picture), `fonts-dejavu-core`
* **Optional:** `culmus` (extra Hebrew fonts)
* **To build:** `dpkg-dev` (method 1), or `debhelper` + `dpkg-dev` (method 2);
  `lintian` to check the package

Works on Debian 11+, Ubuntu 22.04+, Linux Mint 21+ and other Debian-based systems.

## Build the package

### Method 1 – quick (no debhelper)

```sh
sudo apt install dpkg-dev          # usually already installed
./build-deb.sh
```

Result: `dist/playlist-checker_1.6.5_all.deb`

### Method 2 – standard Debian tools

```sh
sudo apt install debhelper dpkg-dev
dpkg-buildpackage -us -uc -b
```

Result: `../playlist-checker_1.6.5_all.deb`

## Install / remove

```sh
sudo apt install ./dist/playlist-checker_1.6.5_all.deb
playlist-checker                    # or find it in the applications menu
sudo apt remove playlist-checker
```

Use `apt install ./file.deb` (not `dpkg -i`) so the dependencies are installed too.
User settings are kept in `~/.config/playlist-checker/settings.json`.

## New version

1. Change `APP_VERSION` in `playlist_checker_gui.py` (e.g. `1.0.1`).
2. Add an entry at the top of `debian/changelog` with the same version
   (`dch -v 1.0.1` or by hand, keeping the exact format).
3. Run `./build-deb.sh` – it refuses to build if the two versions differ.
