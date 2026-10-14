import Foundation
import PDFKit
import AppKit
let args = CommandLine.arguments
let document = PDFDocument(url: URL(fileURLWithPath: args[1]))!
let output = URL(fileURLWithPath: args[2])
try FileManager.default.createDirectory(at: output, withIntermediateDirectories: true)
print("Pages: \(document.pageCount)")
for index in 0..<document.pageCount {
    let page = document.page(at: index)!
    let bounds = page.bounds(for: .mediaBox)
    let scale: CGFloat = 1.5
    let bitmap = NSBitmapImageRep(bitmapDataPlanes: nil, pixelsWide: Int(bounds.width * scale), pixelsHigh: Int(bounds.height * scale), bitsPerSample: 8, samplesPerPixel: 4, hasAlpha: true, isPlanar: false, colorSpaceName: .deviceRGB, bytesPerRow: 0, bitsPerPixel: 0)!
    let context = NSGraphicsContext(bitmapImageRep: bitmap)!
    NSGraphicsContext.saveGraphicsState()
    NSGraphicsContext.current = context
    let cg = context.cgContext
    cg.setFillColor(NSColor.white.cgColor)
    cg.fill(CGRect(x: 0, y: 0, width: bounds.width * scale, height: bounds.height * scale))
    cg.scaleBy(x: scale, y: scale)
    page.draw(with: .mediaBox, to: cg)
    NSGraphicsContext.restoreGraphicsState()
    try bitmap.representation(using: .png, properties: [:])!.write(to: output.appendingPathComponent("page-\(index+1).png"))
    try (page.string ?? "").write(to: output.appendingPathComponent("page-\(index+1).txt"), atomically: true, encoding: .utf8)
}
