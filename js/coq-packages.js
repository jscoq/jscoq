"use strict";

class PackageManager {

    constructor(panel) {
        this.panel   = panel;
        this.bundles = {};
    }

    addPackageInfo(pkg_info) {

        var div  = document.createElement('div');
        var dsel = d3.select(div);

        dsel.data([pkg_info]);

        dsel.append('img')
            .attr('src', 'images/dl.png')
            .on('click', () => { this.startPackageDownload(); });

        dsel.append('span')
            .text(d => d.desc);

        this.panel.appendChild(div);

        var desc = pkg_info.desc;
        var pkgs = pkg_info.pkgs;
        var no_files = 0;

        for(var i = 0; i < pkgs.length; i++)
            no_files += pkgs[i].no_files;

        pkg_info.loaded = 0;
        pkg_info.total  = no_files;

        this.bundles[desc] = { div: div, info: pkg_info };

    }

    // XXX [EG]: This needs to be tweaked, package loading could be
    // externally initiated.
    startPackageDownload() {

        var row = d3.select(d3.event.target.parentNode);
        jsCoq.add_pkg(row.datum().desc);

    }

    // In all the three cases below, evt = progressInfo
    // bundle_name_    : string
    // method pkg_name : string
    // method loaded   : int
    // method total    : int

    onPkgLoadStart(evt) {

        var div  = this.bundles[evt.bundle_name].div;
        // var row  = d3.select(this.panel).selectAll('div')
        //     .filter(pkg => pkg.desc === evt.bundle_name);

        // Workaround, this is called at a finer granularity, add the
        // bar only the first time.

        if (! this.bundles[evt.bundle_name].bar ) {
            var row  = d3.select(div);

            var bar = row.append('div')
                .attr('class', 'rel-pos')
                .append('div')
                .attr('class', 'progressbar');

            var egg = bar
                .append('img')
                .attr('src', 'images/egg.png')
                .attr('class', 'progress-egg');

            this.bundles[evt.bundle_name].bar = bar;
            this.bundles[evt.bundle_name].egg = egg;
        }
    }


    onPkgProgress(evt) {

        var info = this.bundles[evt.bundle_name].info;
        var bar  = this.bundles[evt.bundle_name].bar;
        var egg  = this.bundles[evt.bundle_name].egg;

        var progress = ++info.loaded / info.total;
        var angle    = (progress * 360 * 15) % 360;
        egg.style('transform', 'rotate(' + angle + 'deg)');
        bar.style('width', progress * 100 + '%');
    }

    onPkgLoad(evt) {

        var info = this.bundles[evt.bundle_name].info;

        // Workaround due to bad granularity
        if (info.loaded === info.total) {

            var div  = this.bundles[evt.bundle_name].div;
            var row  = d3.select(div);

            row.select('.rel-pos').remove();
            row.select('img')
                .attr('src', 'images/checked.png');
        }
    }
}

// EG: This will be useful once we move file downloading to javascript.
// PackagesManager

class PackageDowloader {

    constructor(row, panel) {
        this.row = row;
        this.bar = null;
        this.egg = null;
        this.bundle_name = row.datum().desc;
        this.panel = panel;
        this.progress = 0; // percent
    }

    // This method setups the download handling.
    download() {

        // Allow re-download
        // this.row.select('img').on('click', null);

        this.bar = this.row.append('div')
            .attr('class', 'rel-pos')
            .append('div')
            .attr('class', 'progressbar');

        this.egg = this.bar
            .append('img')
            .attr('src', 'images/egg.png')
            .attr('class', 'progress-egg');

        var files_total_length = 0;
        var files_loaded_cpt = 0;
        var pkgs = this.row.datum().pkgs;

        // Proceed to the main download.
        for(var i = 0; i < pkgs.length; i++)
            files_total_length += pkgs[i].no_files;

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
