"""Generate the OG image (1200x630) for social sharing."""
from PIL import Image, ImageDraw, ImageFont
import os

W, H = 1200, 630
img = Image.new('RGB', (W, H), '#1a1a2e')
draw = ImageDraw.Draw(img)

# Try to use a nice font, fall back to default
try:
    title_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 48)
    subtitle_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 24)
    eq_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 72)
    small_font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 18)
except (OSError, IOError):
    title_font = ImageFont.load_default()
    subtitle_font = ImageFont.load_default()
    eq_font = ImageFont.load_default()
    small_font = ImageFont.load_default()

# Equation (centered, prominent)
eq_text = "x\u00b2 = x + 1"
bbox = draw.textbbox((0, 0), eq_text, font=eq_font)
eq_w = bbox[2] - bbox[0]
draw.text(((W - eq_w) / 2, 120), eq_text, fill='#4a90d9', font=eq_font)

# Title
title = "Derive, Discover, Name"
bbox = draw.textbbox((0, 0), title, font=title_font)
t_w = bbox[2] - bbox[0]
draw.text(((W - t_w) / 2, 260), title, fill='#ffffff', font=title_font)

# Subtitle
sub = "A case study in AI-assisted mathematical discovery"
bbox = draw.textbbox((0, 0), sub, font=subtitle_font)
s_w = bbox[2] - bbox[0]
draw.text(((W - s_w) / 2, 330), sub, fill='#adb5bd', font=subtitle_font)

# Stats line
stats = "2,350 theorems  |  25,000 lines of Lean 4  |  0 axioms"
bbox = draw.textbbox((0, 0), stats, font=small_font)
st_w = bbox[2] - bbox[0]
draw.text(((W - st_w) / 2, 400), stats, fill='#6c757d', font=small_font)

# Project name
proj = "The Omega Project"
bbox = draw.textbbox((0, 0), proj, font=small_font)
p_w = bbox[2] - bbox[0]
draw.text(((W - p_w) / 2, 550), proj, fill='#495057', font=small_font)

# Decorative line
draw.line([(200, 240), (1000, 240)], fill='#4a90d9', width=1)

out_path = '/Users/auric/automath/docs/dossier/og-image.png'
img.save(out_path, 'PNG', optimize=True)
print(f"Generated: og-image.png ({os.path.getsize(out_path)} bytes)")
