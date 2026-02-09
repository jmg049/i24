#!/usr/bin/env python3
"""
Script to build AudioSamples Python documentation locally.

Usage:
    python build_docs.py [--clean] [--serve]

Options:
    --clean    Clean the build directory before building
    --serve    Start a local HTTP server to view the docs after building
"""

import argparse
import os
import shutil
import subprocess
import sys
import webbrowser
from http.server import HTTPServer, SimpleHTTPRequestHandler
from pathlib import Path
import threading
import time


def clean_build():
    """Remove the build directory."""
    build_dir = Path(__file__).parent / "docs" / "build"
    if build_dir.exists():
        print(f"Cleaning {build_dir}")
        shutil.rmtree(build_dir)


def build_docs():
    """Build the documentation using Sphinx."""
    docs_dir = Path(__file__).parent / "docs"
    if not docs_dir.exists():
        print("Error: docs directory not found")
        return False

    print("Building documentation with Sphinx...")
    try:
        result = subprocess.run(
            ["make", "html"], cwd=docs_dir, capture_output=True, text=True
        )

        if result.returncode == 0:
            print("Documentation built successfully!")
            html_dir = docs_dir / "build" / "html"
            print(f"Documentation available at: {html_dir / 'index.html'}")
            return True
        else:
            print("Error building documentation:")
            print(result.stdout)
            print(result.stderr)
            return False

    except subprocess.CalledProcessError as e:
        print(f"Error running make: {e}")
        return False


def serve_docs(port=8000):
    """Start a local HTTP server to view the documentation."""
    html_dir = Path(__file__).parent / "docs" / "build" / "html"

    if not html_dir.exists():
        print("Error: Built documentation not found. Run build first.")
        return False

    os.chdir(html_dir)

    class CustomHandler(SimpleHTTPRequestHandler):
        def log_message(self, format, *args):
            # Suppress server logs
            pass

    server = HTTPServer(("localhost", port), CustomHandler)

    def start_server():
        print(f"Serving documentation at http://localhost:{port}")
        print("Press Ctrl+C to stop the server")
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            print("\nStopping server...")
            server.server_close()

    # Start server in a separate thread
    server_thread = threading.Thread(target=start_server, daemon=True)
    server_thread.start()

    # Open browser after a short delay
    time.sleep(1)
    url = f"http://localhost:{port}"
    print(f"Opening {url} in browser...")
    webbrowser.open(url)

    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        print("\nShutting down...")
        server.server_close()

    return True


def main():
    parser = argparse.ArgumentParser(
        description="Build AudioSamples Python documentation"
    )
    parser.add_argument(
        "--clean", action="store_true", help="Clean build directory first"
    )
    parser.add_argument(
        "--serve", action="store_true", help="Serve docs locally after building"
    )
    parser.add_argument(
        "--port", type=int, default=8000, help="Port for local server (default: 8000)"
    )

    args = parser.parse_args()

    if args.clean:
        clean_build()

    # Build documentation
    if not build_docs():
        sys.exit(1)

    # Serve if requested
    if args.serve:
        serve_docs(args.port)


if __name__ == "__main__":
    main()
