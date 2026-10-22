# Generate experience-text glyph PNGs using the game's actual GDI font.
#
# The game's Font object uses SysFont with face "Arial Unicode MS". The original
# in-game text size corresponds to HFONT height -20 @96dpi, i.e. 15pt with
# GraphicsUnit.Point. We render each glyph with GDI TextOutA so the pixels and
# advances match the game exactly, then export white+alpha PNGs for
# NativeDrawExpGlyphs (DrawImage path, no shared DC).
#
# Usage:
#   powershell -ExecutionPolicy Bypass -File gen_gdi_glyphs.ps1
#   powershell -ExecutionPolicy Bypass -File gen_gdi_glyphs.ps1 -PointSize 16
#
# After changing PointSize, update g_expGlyphDefs in pch.cpp with the printed
# advance/dx/dy values.

param(
    [float]$PointSize = 15.0,
    [string]$Face = 'Arial Unicode MS',
    [switch]$Bold,
    [string]$OutDir = (Join-Path $PSScriptRoot '')
)

Add-Type -AssemblyName System.Drawing
Add-Type -ReferencedAssemblies System.Drawing @"
using System;
using System.Drawing;
using System.Drawing.Imaging;
using System.IO;
using System.Runtime.InteropServices;
public static class GenGdiGlyphs {
  [DllImport("gdi32.dll")] public static extern IntPtr SelectObject(IntPtr hdc, IntPtr obj);
  [DllImport("gdi32.dll")] public static extern bool DeleteObject(IntPtr obj);
  [DllImport("gdi32.dll")] public static extern bool TextOutA(IntPtr hdc, int x, int y, string s, int n);
  [DllImport("gdi32.dll")] public static extern bool GetTextExtentPoint32A(IntPtr hdc, string s, int n, out SIZE sz);
  [DllImport("gdi32.dll")] public static extern int SetBkMode(IntPtr hdc, int mode);
  [DllImport("gdi32.dll")] public static extern int SetTextColor(IntPtr hdc, int color);
  [StructLayout(LayoutKind.Sequential)] public struct SIZE { public int cx, cy; }
  public static string Run(string outDir, float pt, string face, bool bold) {
    Directory.CreateDirectory(outDir);
    var font = new Font(face, pt, bold ? FontStyle.Bold : FontStyle.Regular, GraphicsUnit.Point);
    IntPtr hfont = font.ToHfont();
    string chars = "0123456789Lv.";
    var sb = new System.Text.StringBuilder();
    foreach (char ch in chars) {
      string s = ch.ToString();
      int W=96,H=96;
      using (var bmp = new Bitmap(W,H,PixelFormat.Format32bppArgb)) {
        using (var g = Graphics.FromImage(bmp)) {
          g.Clear(Color.Black);
          IntPtr hdc = g.GetHdc();
          IntPtr old = SelectObject(hdc, hfont);
          SetBkMode(hdc, 1); // TRANSPARENT
          SetTextColor(hdc, 0x00FFFFFF);
          SIZE sz; GetTextExtentPoint32A(hdc, s, 1, out sz);
          TextOutA(hdc, 24, 24, s, 1);
          SelectObject(hdc, old);
          g.ReleaseHdc(hdc);
          var bd = bmp.LockBits(new Rectangle(0,0,W,H), ImageLockMode.ReadOnly, PixelFormat.Format32bppArgb);
          var data = new byte[bd.Stride*H]; Marshal.Copy(bd.Scan0,data,0,data.Length); bmp.UnlockBits(bd);
          int minx=W,miny=H,maxx=-1,maxy=-1;
          for(int y=0;y<H;y++) for(int x=0;x<W;x++){int o=y*bd.Stride+x*4;int b=data[o],gg=data[o+1],r=data[o+2];int a=Math.Max(r,Math.Max(gg,b));if(a<=8)continue;if(x<minx)minx=x;if(y<miny)miny=y;if(x>maxx)maxx=x;if(y>maxy)maxy=y;}
          if(maxx<0){sb.Append(ch+": EMPTY\n");continue;}
          int cw=maxx-minx+1,chh=maxy-miny+1;
          using (var outb = new Bitmap(cw,chh,PixelFormat.Format32bppArgb)) {
            for(int y=0;y<chh;y++)for(int x=0;x<cw;x++){int o=(y+miny)*bd.Stride+(x+minx)*4;int b=data[o],gg=data[o+1],r=data[o+2];int a=Math.Max(r,Math.Max(gg,b));outb.SetPixel(x,y,Color.FromArgb(a,255,255,255));}
            string fn="ExpFontGDI_"+((int)ch).ToString("X2")+".png";
            outb.Save(Path.Combine(outDir,fn),ImageFormat.Png);
          }
          sb.Append("'"+ch+"': advance="+sz.cx+" dx="+(minx-24)+" dy="+(miny-24)+"\n");
        }
      }
    }
    DeleteObject(hfont);
    return sb.ToString();
  }
}
"@

Write-Host ("Generating glyphs: face='{0}' point={1} -> {2}" -f $Face, $PointSize, $OutDir)
$result = [GenGdiGlyphs]::Run($OutDir, $PointSize, $Face, $Bold.IsPresent)
Write-Host $result
