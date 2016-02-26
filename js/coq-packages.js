"use strict";

class PackageManager {

    constructor(panel) {
        this.panel = panel;
    }

    addPackageInfo(pkg_info) {

        console.log("update"); console.log(pkg_info);

        return;

        var rows = d3.select(this.panel).selectAll('div')
            .data(pkg_info)
            .enter()
            .append('div');

        var self = this;

        rows.each(function () {
            var row = d3.select(this);
            row.append('img')
                .attr('src', 'images/dl.png')
                .on('click', () => { self.sendCoqPkg(); });

            row.append('span')
                .text(d => d.label);
        });
    }

    // XXX [EG]: This needs to be tweaked, package loading could be
    // externally initiated.
    sendCoqPkg() {
        var row  = d3.select(d3.event.target.parentNode);
        var dl  = new PackageDowloader(row, this.panel);
        dl.download();
    }

} // PackagesManager

class PackageDowloader {

    constructor(row, panel) {
        this.row = row;
        this.bar = null;
        this.egg = null;
        this.bundle_name = row.datum().name;
        this.panel = panel;
        this.progress = 0; // percent
    }

    download() {
        this.row.select('img').on('click', null);
        this.bar = this.row.append('div')
            .attr('class', 'rel-pos')
            .append('div')
            .attr('class', 'progressbar');
        this.egg = this.bar
            .append('img')
            .attr('src', 'images/egg.png')
            .attr('class', 'progress-egg');

        var pkg_json_url = 'coq-pkgs/' + this.bundle_name + '.json';
        var req = new XMLHttpRequest();
        req.open('GET', pkg_json_url);
        req.onreadystatechange = () => {
            if (req.readyState === 4) {
                if (req.status === 200 || req.status === 0)
                    this._download(JSON.parse(req.responseText));
                // XXX by design we could not access CoqPanel.log
                // TODO: else log error message
            }
        };
        req.send(null);
    }

    _download(json) {
        var files_total_length = 0;
        var files_loaded_cpt = 0;
        var pkgs = json.pkgs;

        // XXX: Circular dependencies will kill us here.
        var deps = json.deps;

        if (deps) {
            var deps_row = d3.select(this.panel).selectAll('div')
            //                       ^^^^^^^^^^ ummm
                .filter( pkg_row => deps.includes(pkg_row.name) );

            deps_row.forEach( pkg_row =>
                              {   // Pain XXX
                                  if (pkg_row[0]) {
                                      new PackageDowloader(d3.select(pkg_row[0]), this.panel)
                                          .download(); }
                              } );
        }

        // Proceed to the main download.
        for(var i = 0; i < pkgs.length; i++)
            files_total_length += pkgs[i].vo_files.length + pkgs[i].cma_files.length;

        document.body.addEventListener('pkgProgress',
            (evt) => {
                if(evt.detail.bundle_name === this.bundle_name) {
                    this.progress = ++files_loaded_cpt / files_total_length;
                    this.updateProgress();
                    if (files_loaded_cpt === files_total_length)
                        this.finishDownload();
                }
            }
        );
        jsCoq.add_pkg(this.bundle_name);
    }

    updateProgress() {
        var angle = (this.progress * 360 * 15) % 360;
        this.egg.style('transform', 'rotate(' + angle + 'deg)');
        this.bar.style('width', this.progress * 100 + '%');
    }

    finishDownload() {
        this.row.select('.rel-pos').remove();
        this.row.select('img')
            .attr('src', 'images/checked.png');
    }
}

// Local Variables:
// js-indent-level: 4
// End:
